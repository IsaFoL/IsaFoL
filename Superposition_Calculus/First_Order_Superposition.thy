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

    infinite_variable_universe: "infinite (UNIV :: 'v set)" and

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


lemma less\<^sub>t_context_compatible [simp]:
  assumes 
    "term\<^sub>1 \<prec>\<^sub>t term\<^sub>2"
    "is_ground_term term\<^sub>1"
    "is_ground_term term\<^sub>2"
    "is_ground_context context"
  shows 
    "context\<langle>term\<^sub>1\<rangle> \<prec>\<^sub>t context\<langle>term\<^sub>2\<rangle>"
  using assms
  unfolding less\<^sub>t_less\<^sub>t\<^sub>G[OF assms(2, 3)]
  by (metis ground_term_with_context(1) ground_term_with_context_is_ground(4) less\<^sub>t\<^sub>G_context_compatible less\<^sub>t_less\<^sub>t\<^sub>G)

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

lemma testing2:  "context\<langle>term\<rangle> \<cdot>t \<theta> = (context \<cdot>t\<^sub>c \<theta>)\<langle>term  \<cdot>t \<theta>\<rangle>"
  by auto

lemma not_Var:  "\<not> is_Var term \<Longrightarrow> \<not> is_Var (context\<langle>term\<rangle>)"
  using ctxt_apply_term.elims by blast

lemma x: "\<not> is_Var (to_term term\<^sub>G)"
  using gterm_is_fun.

lemma sth: "term \<cdot>t \<theta> = term' \<Longrightarrow> is_Var term' \<Longrightarrow> is_Var term"
  apply auto
  by (metis is_Var_def subst_apply_eq_Var)

lemma var_in_term':
  assumes "var \<in> vars_term term"
  obtains "context" where "term = context\<langle>Var var\<rangle>"
  using assms
proof(induction "term")
  case Var
  then show ?case
    by (metis Term.term.simps(17) ctxt_apply_term.simps(1) singletonD)
next
  case (Fun f args)
  then obtain term' where "term' \<in> set args " "var \<in> vars_term term'"
    by (metis term.distinct(1) term.sel(4) term.set_cases(2))

  moreover then obtain args1 args2 where
    "args1 @ [term'] @ args2 = args"
    by (metis append_Cons append_Nil split_list)

  moreover then have "(More f args1 \<box> args2)\<langle>term'\<rangle> = Fun f args"
    by simp

  ultimately show ?case 
    using Fun(1)[of term']
    by (metis Fun.prems(1) append_Cons ctxt_apply_term.simps(2))
qed
 
lemma var_in_term: 
  assumes "\<not> is_ground_term term"
  obtains "context" var where "term = context\<langle>var\<rangle>" "is_Var var"
proof-
  obtain var where "var \<in> vars_term term"
    using assms
    by blast

  moreover then obtain "context" where "term = context\<langle>Var var\<rangle>"
    using var_in_term'
    by metis

  ultimately show ?thesis
    using that
    by blast
qed  

lemma something':  
  assumes 
    not_ground: "\<not> is_ground_term (Fun f terms)" and
    grounding: "is_ground_term ((Fun f terms) \<cdot>t \<theta>)" 
  obtains "term" context\<^sub>G term\<^sub>G
  where
    "term \<in> set terms"
    "\<not> is_ground_term term" 
  by (meson Term.ground.simps(2) Term.ground_vars_term_empty not_ground)

lemma something:  
  assumes 
    not_ground: "\<not> is_ground_term (Fun f terms)" and
    grounding: "is_ground_term ((Fun f terms) \<cdot>t \<theta>)" 
  obtains "term" context\<^sub>G term\<^sub>G
  where
    "term \<in> set terms"
    "\<not> is_ground_term term" 
    "term \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle>"
proof-
  obtain "term" where
    "term \<in> set terms"
    "\<not> is_ground_term term" 
    using something'[OF not_ground grounding].

  moreover then have "is_ground_term (term \<cdot>t \<theta>)"
    using grounding
    by (meson is_ground_iff term.set_intros(4))

  moreover then obtain context\<^sub>G term\<^sub>G where "term \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<rangle>"
    by (metis ctxt_apply_term.simps(1) ctxt_of_gctxt.simps(1) to_ground_term_inverse)

  ultimately show ?thesis 
    using that
    by blast
qed

lemma testis: 
  assumes "\<not> is_ground_term (Fun f terms)" 
  obtains "term" where
    "term \<in> set terms"
    "\<not> is_ground_term term"
  by (meson Term_Context.ground.simps(2) assms is_ground_term_iff_term_context_ground)

lemma context_compose_is_ground:
  assumes "is_ground_context (context \<circ>\<^sub>c context')"
  shows "is_ground_context context" "is_ground_context context'"
  using assms
  by (metis Subterm_and_Context.ctxt_ctxt assms ground_ctxt_apply ground_term_of_gterm is_ground_term_ctxt_iff_ground_ctxt)+

lemma mustbe': 
  assumes "\<not> is_ground_term (Fun f terms)"
  shows "\<exists>term \<in> set terms. \<not> is_ground_term term"
proof(rule ccontr)
  assume "\<not> (\<exists>term\<in>set terms. \<not>  is_ground_term term)"
  then have "\<forall>term \<in>set terms. is_ground_term term"
    by blast

  then have "is_ground_term (Fun f terms)"
    by auto

  then show False 
    using assms
    by blast
qed

lemma mustbe: 
  assumes "\<not> is_ground_term (Fun f terms)"
  obtains ts1 var ts2 where "terms = ts1 @ [var] @ ts2"  "\<not> is_ground_term var"
  using mustbe'
  by (metis append.left_neutral append_Cons assms split_list)

lemma  (in first_order_superposition_calculus) smaller_term: 
  assumes "term \<prec>\<^sub>t term'"
  shows 
    "term \<approx> term\<^sub>2 \<prec>\<^sub>l term' \<approx> term\<^sub>2"
    "term !\<approx> term\<^sub>2 \<prec>\<^sub>l term' !\<approx> term\<^sub>2"
  unfolding less\<^sub>l_def
   apply auto
  using assms
  apply (metis add_mset_add_single multi_member_last multi_self_add_other_not_self one_step_implies_multp set_mset_add_mset_insert set_mset_empty singletonD)
  by (smt (verit) add_mset_add_single add_mset_commute assms asymp_on_subset irreflp_on_if_asymp_on less\<^sub>t_asymmetric less\<^sub>t_transitive multp_cancel_add_mset multp_double_doubleI multp_singleton_singleton top_greatest)

(* TODO: ! *)
lemma trickle:
  assumes "asymp R" "transp R" "R x y" "multp R X Y"
  shows "multp R (add_mset x X) (add_mset y Y)"
  using assms(3, 4)
  unfolding multp_eq_multp\<^sub>H\<^sub>O[OF assms(1, 2)]
  unfolding multp\<^sub>H\<^sub>O_def
proof-
  assume a: "R x y" "X \<noteq> Y \<and> (\<forall>y. count Y y < count X y \<longrightarrow> (\<exists>x. R y x \<and> count X x < count Y x))"

  then have "x \<noteq> y"
    using assms(1) unfolding asymp_on_def
    by blast

  with a have "add_mset x X \<noteq> add_mset y Y"
    by (metis assms(1) asympD count_add_mset lessI less_not_refl)

  moreover have "\<And>y'. count (add_mset y Y) y' < count (add_mset x X) y' \<Longrightarrow> \<exists>x'. R y' x' \<and> count (add_mset x X) x' < count (add_mset y Y) x'"
  proof-
    fix x'
    assume "count (add_mset y Y) x' < count (add_mset x X) x'"

    show "\<exists>x''. R x' x'' \<and> count (add_mset x X) x'' < count (add_mset y Y) x''"
    proof(cases "x' = x")
      case True
      
      then show ?thesis 
        apply auto
        by (metis a(2) assms(1) assms(2) assms(3) asympD not_less_eq transpE)
    next
      case False
     
      then show ?thesis
        apply auto
        by (metis \<open>count (add_mset y Y) x' < count (add_mset x X) x'\<close> a(2) assms(1) assms(2) assms(3) asympD count_add_mset less_Suc_eq not_less_eq transpE)
    qed
  qed
  
  ultimately show "add_mset x X \<noteq> add_mset y Y \<and> (\<forall>ya. count (add_mset y Y) ya < count (add_mset x X) ya \<longrightarrow> (\<exists>xa. R ya xa \<and> count (add_mset x X) xa < count (add_mset y Y) xa))"
    by blast
qed

lemma  (in first_order_superposition_calculus) smaller_literal': 
  assumes "literal \<prec>\<^sub>l literal'" "clause \<preceq>\<^sub>c clause'"
  shows "add_mset literal clause \<prec>\<^sub>c add_mset literal' clause'"
  using assms trickle
  by (metis add_mset_add_single less\<^sub>l_asymmetric less\<^sub>l_transitive multp\<^sub>H\<^sub>O_plus_plus multp_eq_multp\<^sub>H\<^sub>O multp_singleton_singleton reflclp_iff)
  
lemma  (in first_order_superposition_calculus) smaller_literal: 
  assumes "literal \<prec>\<^sub>l literal'"
  shows "add_mset literal clause \<prec>\<^sub>c add_mset literal' clause"
  using smaller_literal'[OF assms, of clause clause]
  by auto

lemma atom_subst_eq:
  assumes "\<And>x. x \<in> vars_atom atom \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "atom \<cdot>a \<sigma> = atom \<cdot>a \<tau>"
  using term_subst_eq assms
  unfolding vars_atom_def subst_atom_def
  by (metis (no_types, lifting) UN_I uprod.map_cong0)

lemma literal_subst_eq:
  assumes "\<And>x. x \<in> vars_literal literal \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "literal \<cdot>l \<sigma> = literal \<cdot>l \<tau>"
  using atom_subst_eq assms
  unfolding vars_literal_def subst_literal_def
  by (metis literal.map_cong set_literal_atm_of singletonD)

lemma clause_subst_eq:
  assumes "\<And>x. x \<in> vars_clause clause \<Longrightarrow> \<sigma> x = \<tau> x"
  shows "clause \<cdot> \<sigma> = clause \<cdot> \<tau>"
  using literal_subst_eq assms
  unfolding vars_clause_def subst_clause_def
  by (metis (mono_tags, lifting) UN_I multiset.map_cong0)

lemma (in ground_superposition_calculus) less_trm_compatible_with_gctxt':
  assumes "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G"
  shows "t \<prec>\<^sub>t t'"
proof(rule ccontr)
  assume "\<not> t \<prec>\<^sub>t t'"
  then have "t' \<preceq>\<^sub>t t"
    using totalpD by fastforce    

  show False
  proof(cases "t' = t")
    case True
    then have "ctxt\<langle>t\<rangle>\<^sub>G = ctxt\<langle>t'\<rangle>\<^sub>G"
      by blast
    then show False
      using assms
      by (metis insert_iff irreflp_on_def irreflp_on_less_trm)
  next
    case False
    then have "t' \<prec>\<^sub>t t"
      using \<open>t' \<preceq>\<^sub>t t\<close> by fastforce

    then have "ctxt\<langle>t'\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
      using less_trm_compatible_with_gctxt
      by force
      
    then show ?thesis
      using assms
      by (meson asympD asymp_less_trm)
  qed
qed

lemma (in ground_superposition_calculus) context_less:
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<preceq>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms
  by (metis less_trm_compatible_with_gctxt reflclp_iff transpE transp_less_trm)

lemma (in ground_superposition_calculus) context_less':
  assumes 
    "\<And>t. ctxt\<langle>t\<rangle>\<^sub>G \<preceq>\<^sub>t ctxt'\<langle>t\<rangle>\<^sub>G"
    "t \<prec>\<^sub>t t'"
  shows "ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt'\<langle>t'\<rangle>\<^sub>G"
  using assms
  by (meson less_trm_compatible_with_gctxt transpD_strict_non_strict transp_less_trm)

lemma (in ground_superposition_calculus) fun_less:
  assumes 
    "\<forall>term \<in> set terms. g term \<preceq>\<^sub>t term"
    "\<exists>term \<in> set terms. g term \<prec>\<^sub>t term"
    "\<And>term. g (g term) = g term"
  shows "GFun f (map g terms) \<prec>\<^sub>t GFun f terms"
  using assms
proof(induction "filter (\<lambda>term. g term \<prec>\<^sub>t term) terms" arbitrary: terms)
  case Nil
  then show ?case
    unfolding empty_filter_conv
    by blast
next
  case first: (Cons t ts)
  
  show ?case
  proof(cases ts)
    case Nil
    then obtain ss1 ss2 where
      terms: "terms = ss1 @ t # ss2"
      using filter_eq_ConsD[OF  first.hyps(2)[symmetric]]
      by blast

    then have a: "\<forall>term \<in> set ss1. g term = term"
      using first.hyps(2) first.prems(1) Nil
      by (metis (no_types, lifting) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD reflclp_iff set_append)

    from terms have b: "\<forall>term \<in> set ss2. g term = term"
      using first.hyps(2) first.prems(1)
      by (metis (no_types, lifting) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD list.set_intros(2) local.Nil reflclp_iff set_append)
    
    from a b have g_terms: "map g terms = ss1 @ g t # ss2"
      by (simp add: map_idI terms)

    have less: "g t \<prec>\<^sub>t t" 
      using first.hyps(2)
      by (metis filter_eq_ConsD)

    have "(GMore f ss1 \<box>\<^sub>G ss2)\<langle>g t\<rangle>\<^sub>G \<prec>\<^sub>t (GMore f ss1 \<box>\<^sub>G ss2)\<langle>t\<rangle>\<^sub>G"
      using less_trm_compatible_with_gctxt[OF less]
      by blast

    then show ?thesis
      unfolding g_terms
      unfolding terms
      by simp
  next
    case (Cons t' ts')
    from first(2) obtain ss1 ss2 where
      terms: "terms = ss1 @ t # ss2" and
      "(\<forall>s\<in>set ss1. \<not>  g s \<prec>\<^sub>t s)" and
      less: "g t \<prec>\<^sub>t t" and 
      "ts = filter (\<lambda>term. g term \<prec>\<^sub>t term) ss2"
      using Cons_eq_filter_iff[of t ts "(\<lambda>term. g term \<prec>\<^sub>t term)"]
      by blast

    let ?terms' = "ss1 @ g t # ss2"

    have "ts = filter (\<lambda>term. g term \<prec>\<^sub>t term) ?terms'"
      by (simp add: \<open>\<forall>s\<in>set ss1. \<not> g s \<prec>\<^sub>t s\<close> \<open>ts = filter (\<lambda>term. g term \<prec>\<^sub>t term) ss2\<close> first.prems(3) irreflpD)

    moreover have "\<forall>term\<in>set ?terms'. g term \<preceq>\<^sub>t term"
      using first.prems(1) first.prems(3) terms by auto

    moreover have "\<exists>term\<in>set ?terms'. g term \<prec>\<^sub>t term"
      using calculation(1) local.Cons neq_Nil_conv by force

    ultimately have terms': "GFun f (map g ?terms') \<prec>\<^sub>t GFun f ?terms'"
      using first.hyps(1) first.prems(3) by blast

    have x: "GFun f (map g (ss1 @ g t # ss2)) =  GFun f (map g (ss1 @ t # ss2))"
      by (simp add: first.prems(3))

    have "(GMore f ss1 \<box>\<^sub>G ss2)\<langle>g t\<rangle>\<^sub>G \<prec>\<^sub>t (GMore f ss1 \<box>\<^sub>G ss2)\<langle>t\<rangle>\<^sub>G"
      using less_trm_compatible_with_gctxt[OF less].

    then have "GFun f (ss1 @ g t # ss2) \<prec>\<^sub>t GFun f (ss1 @ t # ss2)"
      by simp

    with terms' show ?thesis
      unfolding terms x
      by (meson transpE transp_less_trm)
  qed
qed

lemma yeah:
  assumes
    "var \<in> vars_term term"  
    "is_ground_term (term \<cdot>t \<theta>)"
  shows "\<exists>context. to_ground_term (term \<cdot>t \<theta>) = context \<langle>to_ground_term (\<theta> var)\<rangle>\<^sub>G"
  using assms
proof(induction "term")
  case (Var x)
  then show ?case
    apply auto
    by (metis ctxt_apply_term.simps(1) term_of_gterm_ctxt_apply term_of_gterm_inv)
next
  case (Fun f terms)
  then show ?case
    by (smt (verit, best) eval_term.simps(1) term_of_gterm_ctxt_apply testing2 to_ground_term_inverse var_in_term')
qed

lemma (in first_order_superposition_calculus_with_grounding) term_subst_less:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "is_ground_term replacement" and
    "replacement \<prec>\<^sub>t \<theta> var" and
    "is_ground_term (term' \<cdot>t \<theta>)" and
    "var \<in> vars_term term'"
  shows "term' \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term' \<cdot>t \<theta>"
  using assms(3, 4)
proof(induction term')
  case Var
  then show ?case 
    using assms(1, 2)
    by simp
next
  case (Fun f terms)

   have "to_ground_term replacement \<prec>\<^sub>t\<^sub>G to_ground_term (\<theta> var)"
    by (meson assms is_ground_iff less\<^sub>t_less\<^sub>t\<^sub>G)

  have "\<forall>term \<in> set terms. term \<cdot>t \<theta>(var := replacement) \<preceq>\<^sub>t term \<cdot>t \<theta>"
    by (metis Fun.IH Fun.prems(1) eval_with_fresh_var is_ground_iff reflclp_iff term.set_intros(4))

  moreover have "\<exists>term \<in> set terms.  term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>"
    by (smt (verit) Fun.prems(1) Fun.prems(2) assms(2) calculation fun_upd_same is_ground_iff not_less_eq\<^sub>t reflclp_iff term.distinct(1) term.inject(2) term.set_cases(2) term_subst_eq_rev)

  ultimately show ?case
    using Fun(2, 3)
  proof(induction "filter (\<lambda>term. term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>) terms" arbitrary: terms)
    case Nil
    then show ?case
      unfolding empty_filter_conv
      by blast
  next
    case first: (Cons t ts)
    
    show ?case
    proof(cases ts)
      case Nil
      then obtain ss1 ss2 where
        terms: "terms = ss1 @ t # ss2"
        using filter_eq_ConsD[OF first.hyps(2)[symmetric]]
        by blast

      then have a: "\<forall>term \<in> set ss1. term \<cdot>t \<theta>(var := replacement) = term \<cdot>t \<theta>"
        using first.hyps(2) first.prems(1) Nil
        by (smt (verit, del_insts) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD reflclp_iff set_append)

      from terms have b: "\<forall>term \<in> set ss2. term \<cdot>t \<theta>(var := replacement) = term \<cdot>t \<theta>"
        using first.hyps(2) first.prems(1) Nil
        by (smt (verit, del_insts) Un_iff append_Cons_eq_iff filter_empty_conv filter_eq_ConsD list.set_intros(2) reflclp_iff set_append)

      from a b have terms': 
        "map (\<lambda>term. term \<cdot>t \<theta>(var := replacement)) terms = (map (\<lambda>term. term \<cdot>t \<theta>) ss1) @ t \<cdot>t \<theta>(var := replacement) #  (map (\<lambda>term. term \<cdot>t \<theta>) ss2)"
        by (simp add: map_idI terms)

      have less: "t \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t t \<cdot>t \<theta>" 
        using first.hyps(2)
        by (metis filter_eq_ConsD)

      have "is_ground_term (t \<cdot>t \<theta>)"
        using terms first(5)
        by auto

      moreover have "is_ground_term (t \<cdot>t \<theta>(var := replacement))"
        by (metis assms(1) calculation fun_upd_other fun_upd_same is_ground_iff)

      moreover have "is_ground_context (More f (map (\<lambda>term. (term \<cdot>t \<theta>)) ss1) \<box> (map (\<lambda>term. (term \<cdot>t \<theta>)) ss2))"
        using terms first(5)
        by auto

      ultimately obtain context\<^sub>G t'\<^sub>G t\<^sub>G where
        context\<^sub>G: "to_context context\<^sub>G = More f (map (\<lambda>term. (term \<cdot>t \<theta>)) ss1) \<box> (map (\<lambda>term. (term \<cdot>t \<theta>)) ss2)" and 
        t'\<^sub>G: "to_term t'\<^sub>G = t \<cdot>t \<theta>(var := replacement)" and 
        t\<^sub>G: "to_term t\<^sub>G = t \<cdot>t \<theta>"
        by (metis gctxt_of_ctxt_inv is_ground_term_ctxt_iff_ground_ctxt to_ground_term_inverse)

      from less have less\<^sub>G: "t'\<^sub>G \<prec>\<^sub>t\<^sub>G t\<^sub>G" 
        unfolding less\<^sub>t\<^sub>G_less\<^sub>t t'\<^sub>G t\<^sub>G.

      have less': "context\<^sub>G\<langle>t'\<^sub>G\<rangle>\<^sub>G \<prec>\<^sub>t\<^sub>G context\<^sub>G\<langle>t\<^sub>G\<rangle>\<^sub>G"
        using less\<^sub>t\<^sub>G_context_compatible[OF less\<^sub>G].

      have x: "Fun f terms \<cdot>t \<theta>(var := replacement) = (to_context context\<^sub>G)\<langle>to_term t'\<^sub>G\<rangle>"
        unfolding context\<^sub>G t'\<^sub>G terms
        using a b
        by auto

      have x': "Fun f terms \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term t\<^sub>G\<rangle>"
        unfolding context\<^sub>G t\<^sub>G terms
        by auto

      from less' show ?thesis
        unfolding x x' less\<^sub>t\<^sub>G_less\<^sub>t ground_term_with_context(3).
    next
      case (Cons t' ts')
      from first(2) 
      obtain ss1 ss2 where
      terms: "terms = ss1 @ t # ss2" and
      "(\<forall>s\<in>set ss1. \<not> s \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t s \<cdot>t \<theta>)" and
      less: "t \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t t \<cdot>t \<theta>" and 
      "ts = filter (\<lambda>term. term \<cdot>t \<theta>(var := replacement)\<prec>\<^sub>t term \<cdot>t \<theta>) ss2"
        using Cons_eq_filter_iff[of t ts "(\<lambda>term. term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>)"]
        by blast

      let ?terms' = "ss1 @ (t \<cdot>t \<theta>(var := replacement))  # ss2"

      have "ts = filter (\<lambda>term. term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>) ?terms'" 
        apply auto
        apply (smt (verit) Un_iff assms(1) asympD first.prems(3) fun_upd_other fun_upd_same is_ground_iff less\<^sub>t_asymmetric list.set_intros(1) set_append term.set_intros(4) term_subst.subst_ident_if_ground terms)
        by (simp add: \<open>\<forall>s\<in>set ss1. \<not> s \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t s \<cdot>t \<theta>\<close> \<open>ts = filter (\<lambda>term. term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>) ss2\<close>)

      moreover have "\<forall>term \<in> set ?terms'. term \<cdot>t \<theta>(var := replacement) \<preceq>\<^sub>t term \<cdot>t \<theta>"
        using first.prems(1) 
        unfolding terms
        apply auto
        apply (metis (no_types, lifting) Term.term.simps(18) UN_I Un_iff assms(1) first.prems(3) fun_upd_other fun_upd_same is_ground_iff list.set_intros(1) set_append term_subst.subst_ident_if_ground terms)
        by (metis asympD less less\<^sub>t_asymmetric)

      moreover have "\<exists>term \<in> set ?terms'. term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>"
        using calculation(1) Cons neq_Nil_conv by force

      moreover have grounding: "is_ground_term (Fun f ?terms' \<cdot>t \<theta>)"
        apply auto
        apply (metis Term.term.simps(18) UN_I Un_iff assms(1) empty_iff first.prems(3) fun_upd_other fun_upd_same is_ground_iff list.set_intros(1) set_append terms)
        using first.prems(3) terms by fastforce+

      moreover have "var \<in> vars_term (Fun f ?terms')"
        by (metis calculation(3) eval_with_fresh_var irreflpD irreflp_on_if_asymp_on less\<^sub>t_asymmetric term.set_intros(4))

      ultimately have terms': "Fun f ?terms' \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t Fun f ?terms' \<cdot>t \<theta>"
        using first.hyps(1) first.prems(3) by blast

      have x1: "t \<cdot>t \<theta>(var := replacement) \<cdot>t \<theta> = t \<cdot>t \<theta>(var := replacement)"
        by (metis (no_types, lifting) Term.term.simps(18) UN_I Un_iff assms(1) first.prems(3) fun_upd_other fun_upd_same is_ground_iff list.set_intros(1) set_append term_subst.subst_ident_if_ground terms)

      have x2: "t \<cdot>t \<theta>(var := replacement) \<cdot>t \<theta>(var := replacement) = t \<cdot>t \<theta>(var := replacement)"
        by (metis (no_types, lifting) Term.term.simps(18) UN_I Un_iff assms(1) first.prems(3) fun_upd_other fun_upd_same is_ground_iff list.set_intros(1) set_append term_subst.subst_ident_if_ground terms)

      then have x: "Fun f ?terms' \<cdot>t \<theta>(var := replacement) =  Fun f terms \<cdot>t \<theta>(var := replacement)"
        unfolding terms
        by auto

      have t_groundings: "is_ground_term (t \<cdot>t \<theta>(var := replacement))" "is_ground_term (t \<cdot>t \<theta>)" 
        using grounding x1 apply force
        using Term.term.simps(18) UN_I Un_iff first.prems(3) terms by force

      have context_grounding: "is_ground_context (More f ss1 \<box> ss2 \<cdot>t\<^sub>c \<theta>)"
        by (metis ctxt_apply_term.simps(1) ctxt_apply_term.simps(2) ground_term_with_context_is_ground2(1) grounding subst_apply_term_ctxt_apply_distrib)

      have "Fun f (ss1 @ t \<cdot>t \<theta>(var := replacement) # ss2) \<cdot>t \<theta> \<prec>\<^sub>t Fun f terms \<cdot>t \<theta>"
        unfolding terms
        using less\<^sub>t_context_compatible[OF less t_groundings context_grounding] x1
        by auto

      with terms' show ?thesis 
        unfolding terms x
        by (meson transpE less\<^sub>t_transitive)
    qed
  qed
qed

(* TODO !! *)
lemma (in first_order_superposition_calculus_with_grounding) less\<^sub>t_less\<^sub>l:
  assumes 
    "\<forall>term \<in> set_uprod (atm_of literal). term \<cdot>t \<theta>' \<preceq>\<^sub>t term \<cdot>t \<theta>"
    "\<exists>term \<in> set_uprod (atm_of literal). term \<cdot>t \<theta>' \<prec>\<^sub>t term \<cdot>t \<theta>"
  shows "literal \<cdot>l \<theta>' \<prec>\<^sub>l literal \<cdot>l \<theta>"
  using assms
  unfolding less\<^sub>l_def
proof(induction literal)
  case (Pos x)
  then show ?case
    unfolding subst_literal(1)
    apply auto
    apply(cases x)
    apply auto
    unfolding subst_atom
    apply auto
    apply (metis less\<^sub>t_asymmetric less\<^sub>t_transitive multp_singleton_singleton trickle)
    apply (metis add_mset_add_single multi_self_add_other_not_self one_step_implies_multp set_mset_add_mset_insert set_mset_empty singletonD union_single_eq_member)
    apply (meson asympD less\<^sub>t_asymmetric)
    apply (meson asympD less\<^sub>t_asymmetric)
    apply (simp add: less\<^sub>t_asymmetric less\<^sub>t_transitive trickle)
    apply (meson asympD less\<^sub>t_asymmetric)
    apply (metis irreflp_on_if_asymp_on less\<^sub>t_asymmetric_on less\<^sub>t_transitive multp_cancel_add_mset multp_singleton_singleton)
    by (metis asympD less\<^sub>t_asymmetric_on)
next
  case (Neg x)
  then show ?case
  unfolding subst_literal(2)
  apply auto
  apply(cases x)
  apply auto
  unfolding subst_atom
  apply auto
  apply (simp add: less\<^sub>t_asymmetric less\<^sub>t_transitive trickle)
  apply (smt (verit) add_mset_add_single add_mset_commute irreflp_on_if_asymp_on less\<^sub>t_asymmetric_on less\<^sub>t_transitive multp_cancel_add_mset multp_double_doubleI multp_singleton_singleton)
  apply (meson asympD less\<^sub>t_asymmetric)
  apply (meson asympD less\<^sub>t_asymmetric)
  apply (simp add: less\<^sub>t_asymmetric less\<^sub>t_transitive trickle)
  apply (meson asympD less\<^sub>t_asymmetric)
  apply (smt (verit) add_mset_add_single add_mset_commute irreflp_on_if_asymp_on less\<^sub>t_asymmetric_on less\<^sub>t_transitive multp_cancel_add_mset multp_double_doubleI multp_singleton_singleton)
  by (meson asympD less\<^sub>t_asymmetric)
qed

lemma (in first_order_superposition_calculus_with_grounding) literal_subst_less:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "is_ground_term replacement" and
    "replacement \<prec>\<^sub>t \<theta> var" and
    "is_ground_literal (literal \<cdot>l \<theta>)" and
    "var \<in> vars_literal literal"
  shows "literal \<cdot>l \<theta>(var := replacement) \<prec>\<^sub>l literal \<cdot>l \<theta>"
proof-

  have all_ground_terms: "\<forall>term\<in>set_uprod (atm_of literal). is_ground_term (term \<cdot>t \<theta>)"
    using assms(3) 
    by (metis (mono_tags, lifting) SUP_bot_conv(2) image_iff literal.map_sel(1) literal.map_sel(2) subst_atom_def subst_literal_def uprod.set_map vars_atom_def vars_literal_def)

  then have "\<forall>term \<in> set_uprod (atm_of literal). var \<in> vars_term term \<longrightarrow> term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>"
    using term_subst_less[of replacement \<theta>, OF assms(1, 2)]
    by blast

  moreover have
    "\<forall>term \<in> set_uprod (atm_of literal). var \<notin> vars_term term \<longrightarrow> term \<cdot>t \<theta>(var := replacement) = term \<cdot>t \<theta>"
    by (meson eval_with_fresh_var)  

  ultimately have a: "\<forall>term \<in> set_uprod (atm_of literal). term \<cdot>t \<theta>(var := replacement) \<preceq>\<^sub>t term \<cdot>t \<theta>" 
    by blast

  have b: "\<exists>term \<in> set_uprod (atm_of literal). term \<cdot>t \<theta>(var := replacement) \<prec>\<^sub>t term \<cdot>t \<theta>"
    using assms(2, 4)
    using term_subst_less[of replacement \<theta>, OF assms(1, 2)] all_ground_terms
    unfolding vars_literal_def vars_atom_def 
    by blast

  show ?thesis
    using less\<^sub>t_less\<^sub>l[OF a b].
qed

lemma multp_add_same:
  assumes 
    "asymp R" "transp R" "multp R X Y"
  shows "multp R (add_mset x X) (add_mset x Y)"
  by (meson assms asymp_on_subset irreflp_on_if_asymp_on multp_cancel_add_mset top_greatest)


lemmas (in first_order_superposition_calculus_with_grounding) less\<^sub>c_add_same =  
  multp_add_same[OF less\<^sub>l_asymmetric less\<^sub>l_transitive]

lemma (in first_order_superposition_calculus_with_grounding) less_eq\<^sub>l_less_eq\<^sub>c:
  assumes "\<forall>literal \<in># clause. literal \<cdot>l \<theta>' \<preceq>\<^sub>l literal \<cdot>l \<theta>"
  shows "clause \<cdot> \<theta>' \<preceq>\<^sub>c clause \<cdot> \<theta>"
  using assms 
  apply(induction clause)
   apply auto
     apply (metis less\<^sub>l_asymmetric less\<^sub>l_transitive subst_clause_add_mset trickle)
    apply (simp add: less\<^sub>c_add_same subst_clause_add_mset)
   apply (simp add: smaller_literal subst_clause_add_mset)
  by (simp add: subst_clause_add_mset)
  
lemma (in first_order_superposition_calculus_with_grounding) less\<^sub>l_less\<^sub>c:
  assumes 
    "\<forall>literal \<in># clause. literal \<cdot>l \<theta>' \<preceq>\<^sub>l literal \<cdot>l \<theta>"
    "\<exists>literal \<in># clause. literal \<cdot>l \<theta>' \<prec>\<^sub>l literal \<cdot>l \<theta>"
  shows "clause \<cdot> \<theta>' \<prec>\<^sub>c clause \<cdot> \<theta>"
  using assms
proof(induction clause)
  case empty
  then show ?case by auto
next
  case (add literal clause)
  then have less_eq: "\<forall>literal \<in># clause. literal \<cdot>l \<theta>' \<preceq>\<^sub>l literal \<cdot>l \<theta>"
    by (metis add_mset_remove_trivial in_diffD)

  show ?case 
  proof(cases "literal \<cdot>l \<theta>' \<prec>\<^sub>l literal \<cdot>l \<theta>")
    case True
    moreover have "clause \<cdot> \<theta>' \<preceq>\<^sub>c clause \<cdot> \<theta>"
      using less_eq\<^sub>l_less_eq\<^sub>c[OF less_eq].

    ultimately show ?thesis
      using smaller_literal'
      unfolding subst_clause_add_mset
      by blast
  next
    case False
    then have less: "\<exists>literal \<in># clause. literal \<cdot>l \<theta>' \<prec>\<^sub>l literal \<cdot>l \<theta>"
      using add.prems(2) by auto

   from False have eq: "literal \<cdot>l \<theta>' = literal \<cdot>l \<theta>"
      using add.prems(1) by force

   show ?thesis
     using add(1)[OF less_eq less]
     unfolding subst_clause_add_mset eq
     using less\<^sub>c_add_same
     by blast
  qed
qed

lemma (in first_order_superposition_calculus_with_grounding) clause_subst_less:
  assumes 
    "is_ground_term replacement" and
    "replacement \<prec>\<^sub>t \<theta> var" and
    "is_ground_clause (clause \<cdot> \<theta>)" and
    "var \<in> vars_clause clause"
  shows "clause \<cdot> \<theta>(var := replacement) \<prec>\<^sub>c clause \<cdot> \<theta>"
proof-
  have all_ground_literals: "\<forall>literal \<in># clause. is_ground_literal (literal \<cdot>l \<theta>)"
    using assms(3)
    using ground_literal_in_ground_clause_subst by blast

  then have "\<forall>literal \<in># clause. var \<in> vars_literal literal \<longrightarrow> literal \<cdot>l \<theta>(var := replacement) \<prec>\<^sub>l literal \<cdot>l \<theta>"
    using literal_subst_less[of replacement \<theta>, OF assms(1, 2)]
    by blast

  then have a: "\<forall>literal \<in># clause. literal \<cdot>l \<theta>(var := replacement) \<preceq>\<^sub>l literal \<cdot>l \<theta>"
    by (metis fun_upd_other literal_subst_eq reflclp_iff)

  have b: "\<exists>literal \<in># clause. literal \<cdot>l \<theta>(var := replacement) \<prec>\<^sub>l literal \<cdot>l \<theta>"
    using assms(2, 4)
    using literal_subst_less[of replacement \<theta>, OF assms(1, 2)] all_ground_literals
    unfolding vars_clause_def
    by blast

  show ?thesis
    using less\<^sub>l_less\<^sub>c[OF a b].
qed

lemma (in first_order_superposition_calculus_with_grounding) context_less:
  assumes 
    "is_ground_context context" 
    "is_ground_term term" 
    "is_ground_term term'" 
    "context\<langle>term\<rangle> \<prec>\<^sub>t context\<langle>term'\<rangle>"
  shows "term \<prec>\<^sub>t term'"
  using ground.less_trm_compatible_with_gctxt'
  by (metis assms ground_term_with_context(1) ground_term_with_context_is_ground(4) less\<^sub>t_less\<^sub>t\<^sub>G)

lemma term_subst_if_sth:
  assumes "var \<notin> vars_term term"
  shows "term \<cdot>t (\<lambda>var'. if var' = var then term' else \<theta> var') = term \<cdot>t \<theta>"
  using assms
  by(induction "term") simp_all

lemma atom_subst_if_sth:
  assumes "var \<notin> vars_atom atom"
  shows "atom \<cdot>a (\<lambda>var'. if var' = var then term else \<theta> var') = atom \<cdot>a \<theta>"
  using assms term_subst_if_sth
  unfolding vars_atom_def subst_atom_def
  by (metis (no_types, lifting) UN_I term_subst_eq uprod.map_cong0)

lemma literal_subst_if_sth:
  assumes "var \<notin> vars_literal literal"
  shows "literal \<cdot>l (\<lambda>var'. if var' = var then term else \<theta> var') = literal \<cdot>l \<theta>"
   using assms atom_subst_if_sth
   unfolding vars_literal_def subst_literal_def
   apply(cases literal)
   by fastforce+

lemma clause_subst_if_sth:
  assumes "var \<notin> vars_clause clause"
  shows "clause \<cdot> (\<lambda>var'. if var' = var then term else \<theta> var') = clause \<cdot> \<theta>"
   using assms literal_subst_if_sth
   unfolding vars_clause_def subst_clause_def
   apply auto
   by (smt (verit) image_mset_cong literal_subst_eq)


lemma term_subst_if_sth':
  assumes "is_ground_term term'" "is_ground_term (term \<cdot>t \<theta>)" 
  shows "is_ground_term (term \<cdot>t (\<lambda>var'. if var' = var then term' else \<theta> var'))"
  using assms
  by (simp add: is_ground_iff)


lemma atom_subst_if_sth':
  assumes "is_ground_term term" "is_ground_atom (atom \<cdot>a \<theta>)" 
  shows "is_ground_atom (atom \<cdot>a (\<lambda>var'. if var' = var then term else \<theta> var'))"
  using assms(2) term_subst_if_sth'[OF assms(1)]
  unfolding subst_atom_def vars_atom_def
  by (smt (verit, ccfv_SIG) SUP_bot_conv(2) UN_extend_simps(10) term_subst_eq uprod.set_map)
 
lemma literal_subst_if_sth':
  assumes "is_ground_term term" "is_ground_literal (literal \<cdot>l \<theta>)" 
  shows "is_ground_literal (literal \<cdot>l (\<lambda>var'. if var' = var then term else \<theta> var'))"
  using assms(2) atom_subst_if_sth'[OF assms(1)]
  unfolding subst_literal_def vars_literal_def
(* TODO *)
proof -
  assume "is_ground_atom (atm_of (map_literal (\<lambda>atom. atom \<cdot>a \<theta>) literal))"
  then show "is_ground_atom (atm_of (map_literal (\<lambda>u. u \<cdot>a (\<lambda>a. if a = var then term else \<theta> a)) literal))"
    by (metis (no_types) \<open>\<And>var atom \<theta>. is_ground_atom (atom \<cdot>a \<theta>) \<Longrightarrow> is_ground_atom (atom \<cdot>a (\<lambda>var'. if var' = var then term else \<theta> var'))\<close> literal.map_sel(1) literal.map_sel(2))
qed

(* TODO: use fun update! *)
lemma clause_subst_if_sth':
  assumes "is_ground_term term" "is_ground_clause (clause \<cdot> \<theta>)" 
  shows "is_ground_clause (clause \<cdot> (\<lambda>var'. if var' = var then term else \<theta> var'))"
  using assms(2) literal_subst_if_sth'[OF assms(1)]
  unfolding subst_clause_def vars_clause_def
  by auto

lemma ahh:
  assumes 
    "is_ground_term replacement"                
    "is_ground_term (t \<cdot>t \<theta>)" 
  shows "var \<notin> vars_term (t \<cdot>t \<theta>(var := replacement))"
  using assms
  by(induction t) auto

lemma ahh2:
  assumes 
    "is_ground_term replacement"                
    "is_ground_term (t \<cdot>t \<theta>)" 
  shows "x \<notin> vars_term (t \<cdot>t \<theta>(var := replacement) \<cdot>t \<theta>)"
  using assms
  by(induction t) auto

lemma replace:
  assumes 
    "refl I"
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<in> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  using assms
  by (metis (full_types) compatible_with_gctxtD relcomp.simps symD trans_refl_imp_O_id)

lemma replace':
  assumes 
    "refl I"
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<notin> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<notin> I"
  using assms
  by (metis replace symD)

lemma vars_term_ms_count:
  assumes "is_ground_term term\<^sub>G"
  shows "size {#var' \<in># vars_term_ms context\<langle>Var var\<rangle>. var' = var#} = Suc (size {#var' \<in># vars_term_ms context\<langle>term\<^sub>G\<rangle>. var' = var#})"
proof(induction "context")
  case Hole
  then show ?case
    using assms
    by (simp add: filter_mset_empty_conv)
next
  case (More f ts1 "context" ts2)
  then show ?case 
    by auto
qed

lemma name:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "refl I"
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (term \<cdot>t \<theta>)" 
    "(to_ground_term (term \<cdot>t \<theta>(var := replacement)), term') \<in> I" 
    "(to_ground_term (\<theta> var), to_ground_term replacement) \<in> I"
  shows
    "Upair (to_ground_term (term \<cdot>t \<theta>)) term' \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
  using assms(7,8)
proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms term))" arbitrary: "term")
  case 0
  from 0(1) have "term \<cdot>t \<theta>(var := replacement) = term \<cdot>t \<theta>"
  proof(induction "term" rule: vars_term_ms.induct)
    case 1
    then show ?case 
      by auto
  next
    case (2 f ts)
    then show ?case
      apply auto
      by (metis (no_types, lifting) filter_mset_empty_conv set_mset_vars_term_ms sum_mset_sum_list term.set_intros(4) vars_term_ms.simps(2))
  qed
    
  then show ?case
    by (metis "0.prems"(2) pair_imageI)
next
  case (Suc n)

  have "var \<in> vars_term term"
    using Suc(2) 
    apply(induction "term")
    using set_mset_vars_term_ms apply fastforce
    by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms zero_less_Suc)

  then obtain c where 
    "term": "term = c\<langle>Var var\<rangle>"
    by (meson var_in_term')

  let ?term = "c\<langle>replacement\<rangle>"


  have 1: "n = size {#var' \<in># vars_term_ms ?term. var' = var#}"
    using Suc(2) vars_term_ms_count[OF assms(5), of var c]
    unfolding "term"
    by auto

  have 2: "is_ground_term (c\<langle>replacement\<rangle> \<cdot>t \<theta>)" 
    using "term" Suc.prems(1) assms(5) by auto
    
  have 3:  "(to_ground_term (c\<langle>replacement\<rangle> \<cdot>t \<theta>(var := replacement)), term') \<in> I"
    using "term" Suc.prems(2) assms(5) by auto

  have 4: "(to_ground_term replacement, to_ground_term (\<theta> var)) \<in> I"
    using assms(9)
    by (meson assms(3) symE)

  show ?case 
    using Suc(1)[OF 1 2 3]
    using replace[OF assms(1, 2, 3, 4) 4, of "to_ground_context (c \<cdot>t\<^sub>c \<theta>)" term']
    by (smt (z3) "term" Upair_inject Suc.prems(1) assms(3) assms(5) case_prod_conv converseE ctxt_of_gctxt_apply_gterm eval_term.simps(1) gctxt_of_ctxt_inv image_iff subst_apply_term_ctxt_apply_distrib sym_conv_converse_eq term_of_gterm_ctxt_apply_ground(1) term_subst.subst_ident_if_ground to_ground_term_inverse)
qed


lemma name':
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "refl I"
    "trans I"
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (term \<cdot>t \<theta>)" 
    "(to_ground_term (term \<cdot>t \<theta>(var := replacement)), term') \<notin> I" 
    "(to_ground_term (\<theta> var), to_ground_term replacement) \<in> I"
  shows
    "Upair (to_ground_term (term \<cdot>t \<theta>)) term' \<notin> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
  using assms(7,8)
proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms term))" arbitrary: "term")
  case 0
  from 0(1) have "term \<cdot>t \<theta>(var := replacement) = term \<cdot>t \<theta>"
  proof(induction "term" rule: vars_term_ms.induct)
    case 1
    then show ?case 
      by auto
  next
    case (2 f ts)
    then show ?case
      apply auto
      by (metis (no_types, lifting) filter_mset_empty_conv set_mset_vars_term_ms sum_mset_sum_list term.set_intros(4) vars_term_ms.simps(2))
  qed
    
  then show ?case
    using "0.prems"(2) assms(3) sym_conv_converse_eq by fastforce
next
  case (Suc n)

  have "var \<in> vars_term term"
    using Suc(2) 
    apply(induction "term")
    using set_mset_vars_term_ms apply fastforce
    by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms zero_less_Suc)

  then obtain c where 
    "term": "term = c\<langle>Var var\<rangle>"
    by (meson var_in_term')

  let ?term = "c\<langle>replacement\<rangle>"


  have 1: "n = size {#var' \<in># vars_term_ms ?term. var' = var#}"
    using Suc(2) vars_term_ms_count[OF assms(5), of var c]
    unfolding "term"
    by auto

  have 2: "is_ground_term (c\<langle>replacement\<rangle> \<cdot>t \<theta>)" 
    using "term" Suc.prems(1) assms(5) by auto
    
  have 3:  "(to_ground_term (c\<langle>replacement\<rangle> \<cdot>t \<theta>(var := replacement)), term') \<notin> I"
    using "term" Suc.prems(2) assms(5) by auto

  have 4: "(to_ground_term replacement, to_ground_term (\<theta> var)) \<in> I"
    using assms(9)
    by (meson assms(3) symE)

  show ?case 
    using Suc(1)[OF 1 2 3]
    using replace'[OF assms(1, 2, 3, 4) 4, of "to_ground_context (c \<cdot>t\<^sub>c \<theta>)" term']
    by (smt (z3) "term" Upair_inject Suc.prems(1) assms(3) assms(5) case_prod_conv converseE ctxt_of_gctxt_apply_gterm eval_term.simps(1) gctxt_of_ctxt_inv image_iff subst_apply_term_ctxt_apply_distrib sym_conv_converse_eq term_of_gterm_ctxt_apply_ground(1) term_subst.subst_ident_if_ground to_ground_term_inverse)
qed


lemma congruence\<^sub>a:
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "refl I"
    "trans I "
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (a \<cdot>t \<theta>)" 
    "is_ground_term (b \<cdot>t \<theta>)" 
    "(to_ground_term (a \<cdot>t \<theta>(var := replacement)), to_ground_term (b \<cdot>t \<theta>(var := replacement))) \<in> I" 
    "(to_ground_term (\<theta> var), to_ground_term replacement) \<in> I"
  shows
    "Upair (to_ground_term (a \<cdot>t \<theta>)) (to_ground_term (b \<cdot>t \<theta>)) \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
  using assms
proof-
  have x: "Upair (to_ground_term (a \<cdot>t \<theta>)) (to_ground_term (b \<cdot>t \<theta>(var := replacement))) \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using name[OF assms(1, 2, 3, 4, 5, 6, 7, 9, 10)].

  then show ?thesis
    using name[OF assms(1, 2, 3, 4, 5, 6, 8)]
    using assms(10) assms(3) sym_conv_converse_eq by fastforce
qed
 
lemma congruence\<^sub>a':
  fixes \<theta> :: "('a, 'b) subst"
  assumes 
    "refl I"
    "trans I "
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_term (a \<cdot>t \<theta>)" 
    "is_ground_term (b \<cdot>t \<theta>)" 
    "(to_ground_term (a \<cdot>t \<theta>(var := replacement)), to_ground_term (b \<cdot>t \<theta>(var := replacement)))\<notin> I" 
    "(to_ground_term (\<theta> var), to_ground_term replacement) \<in> I"
  shows
    "Upair (to_ground_term (a \<cdot>t \<theta>)) (to_ground_term (b \<cdot>t \<theta>)) \<notin>(\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
  using assms
proof-
  have x: "Upair (to_ground_term (a \<cdot>t \<theta>)) (to_ground_term (b \<cdot>t \<theta>(var := replacement))) \<notin>(\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using name'[OF assms(1, 2, 3, 4, 5, 6, 7, 9, 10)].

  then show ?thesis
    using name'[OF assms(1, 2, 3, 4, 5, 6, 8)]
    using assms(10) assms(3) sym_conv_converse_eq by fastforce
qed

lemma congruence\<^sub>L:
  assumes 
    "refl I"
    "trans I "
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_literal (literal \<cdot>l \<theta>)" 
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>(var := replacement))"
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<theta>) \<approx> to_ground_term replacement"
  shows
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>)"
proof(cases literal)
  case (Pos atom)
  then have "to_ground_atom (atom \<cdot>a \<theta>(var := replacement)) \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using assms(8)
    by (metis ground_atom_in_ground_literal2(1) subst_literal(1) true_lit_simps(1))

  then have "to_ground_atom (atom \<cdot>a \<theta>) \<in> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using assms(9)
    unfolding subst_atom_def to_ground_atom_def
    apply(cases atom)
    using congruence\<^sub>a[OF assms(1, 2, 3, 4, 5, 6)]
    by (smt (z3) Pos Upair_inject assms(3) assms(7) case_prodE2 case_prod_conv eval_term.simps(1) ground_terms_in_ground_atom2 image_def literal.sel(1) map_uprod_simps mem_Collect_eq subst_literal(1) symD term_subst_atom_subst true_lit_simps(1) vars_literal_def)

  with Pos show ?thesis
    by (metis ground_atom_in_ground_literal2(1) subst_literal(1) true_lit_simps(1))
next
  case (Neg atom)
  then have "to_ground_atom (atom \<cdot>a \<theta>(var := replacement)) \<notin> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using assms(8)
    by (metis ground_atom_in_ground_literal2(2) subst_literal(2) true_lit_simps(2))

  then have "to_ground_atom (atom \<cdot>a \<theta>) \<notin> (\<lambda>x. case x of (x, xa) \<Rightarrow> Upair x xa) ` I"
    using assms(9)
    unfolding subst_atom_def to_ground_atom_def
    apply(cases atom)
    using congruence\<^sub>a'[OF assms(1, 2, 3, 4, 5, 6)]
    by (smt (z3) Neg Upair_inject assms(3) assms(7) case_prodE2 case_prod_conv eval_term.simps(1) ground_terms_in_ground_atom2 image_def map_uprod_simps mem_Collect_eq subst_literal(2) symD term_subst_atom_subst true_lit_simps(1) upair_in_literal(2) vars_literal_def)

  then show ?thesis
    by (metis Neg ground_atom_in_ground_literal2(2) subst_literal(2) true_lit_simps(2))
qed
  

lemma congruence:
  assumes 
    "refl I"
    "trans I "
    "sym I"
    "compatible_with_gctxt I"
    "is_ground_term replacement" 
    "is_ground_term (Var var \<cdot>t \<theta>)" 
    "is_ground_clause (clause \<cdot> \<theta>)" 
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<theta>(var := replacement))"
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_term (Var var \<cdot>t \<theta>) \<approx> to_ground_term replacement"
  shows
    "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (clause \<cdot> \<theta>)"
  using assms
proof(induction "clause")
  case empty
  then show ?case 
    by auto
next
  case (add literal clause')

  have clause'_grounding: "is_ground_clause (clause' \<cdot> \<theta>)"
    by (metis add.prems(7) is_ground_clause_add_mset subst_clause_add_mset)
  
  show ?case
  proof(cases "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile> to_ground_clause (clause' \<cdot> \<theta>(var := replacement))")
    case True
    show ?thesis 
      using add(1)[OF assms(1 - 6) clause'_grounding True assms(9)]
      by (simp add: subst_clause_add_mset to_ground_clause_def)
  next
    case False
    then have "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>(var := replacement))"
      using add(9)
      by (metis image_mset_add_mset subst_clause_add_mset to_ground_clause_def true_cls_add_mset)

    then have "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_literal (literal \<cdot>l \<theta>)"
      using congruence\<^sub>L
      by (metis add.prems(6) add.prems(7) add.prems(9) assms(1) assms(2) assms(3) assms(4) assms(5) ground_literal_in_ground_clause_subst union_single_eq_member)

    then show ?thesis 
      by (simp add: subst_clause_add_mset to_ground_clause_def)
  qed
qed

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
    not_redundant: (*"non_redundant_superposition premise\<^sub>1 \<rho>\<^sub>1 \<theta>"*)
    "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>))  \<notin> ground.Red_I' (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
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
    by (smt (verit, ccfv_SIG) obtain_from_literal_subst)

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have conclusion_\<theta>\<^sub>G: "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  from literal\<^sub>2_\<theta> have literal\<^sub>2_\<theta>': 
    "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<theta> = to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) to_term_to_atom to_atom_to_literal(2) literal_subst_compose.

  then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<theta>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<theta>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>3"
   using obtain_from_pos_literal_subst
   by metis

  have special_case: "\<nexists>context\<^sub>1 term\<^sub>1. 
    term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
    term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
    context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G  \<and> 
    is_Fun term\<^sub>1 \<Longrightarrow>
      ground.redundant_infer
         (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'] 
                (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')))"
  proof-
    assume a: "\<nexists>context\<^sub>1 term\<^sub>1. 
      term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
      term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
      context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> 
      is_Fun term\<^sub>1"

    have term\<^sub>1_with_context_not_ground: "\<not> is_ground_term term\<^sub>1_with_context"
    proof
      assume "is_ground_term term\<^sub>1_with_context"

      then obtain term\<^sub>1 context\<^sub>1 where
        "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
        "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" 
        "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
        "is_Fun term\<^sub>1"
        by (metis ground_context_is_ground ground_term_is_ground subst_ground_context term\<^sub>1_with_context_\<theta> term_subst.subst_ident_if_ground x)
    
      with a show False
        by blast
    qed

    with a have "\<exists>term\<^sub>x context\<^sub>x context\<^sub>x'. 
      term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle> \<and> 
      is_Var term\<^sub>x \<and> 
      (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>) \<circ>\<^sub>c context\<^sub>x' = to_context context\<^sub>G"
     proof(induction term\<^sub>1_with_context)
       case (Var x)
       then show ?case
         by (metis ctxt_apply_term.simps(1) ctxt_compose.simps(1) subst_apply_ctxt.simps(1) term.disc(1))
     next
       case (Fun f terms)
       then show ?case
         sorry
     qed
  
    then obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
      context\<^sub>x: "term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle>"
      "is_Var term\<^sub>x"
      "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
      by (metis context_compose_is_ground(2) ground_context_is_ground subst_compose_ctxt_compose_distrib subst_ground_context)

    then obtain var\<^sub>x where var\<^sub>x: "Var var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1"
      by (metis eval_term.simps(1) is_Var_def renaming(1) sth subst_compose_def term_subst.is_renaming_def)

    obtain \<theta>' where \<theta>':
      "\<theta>' = \<theta>(var\<^sub>x := (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>)"
      by simp

    have replacement_grounding: "is_ground_term (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      by (metis context\<^sub>x(3) context_compose_is_ground(2) ground_context_is_ground ground_term_is_ground ground_term_with_context_is_ground3 subst_compose_ctxt_compose_distrib)

    have premise\<^sub>1_grounding': "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1 premise\<^sub>1_grounding by blast

    have \<theta>'_grounding: "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
      using clause_subst_if_sth'[OF replacement_grounding premise\<^sub>1_grounding']
      unfolding \<theta>'
      by (smt (verit, ccfv_SIG) clause_subst_eq fun_upd_apply)
 
    let ?D = "to_ground_clause ((add_mset literal\<^sub>1 premise\<^sub>1') \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
    let ?DD = "{ ?D }"

    have term\<^sub>x_\<theta>: "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
      using term\<^sub>1_with_context_\<theta>
      unfolding context\<^sub>x(1)context\<^sub>x(3)[symmetric]
      apply auto
      by (metis ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) replacement_grounding to_term_inverse)

    have term\<^sub>x_\<theta>': "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>') = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
      unfolding \<theta>'
      by (metis eval_term.simps(1) fun_upd_same ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) replacement_grounding to_term_inverse var\<^sub>x)

    have premise\<^sub>1_\<theta>_x: "add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>1) (to_clause premise\<^sub>G\<^sub>1')"
      using premise\<^sub>1 premise\<^sub>1_\<theta> to_clause_add_mset by auto

    have entails: "\<And>I. refl I \<Longrightarrow>
         trans I \<Longrightarrow>
         sym I \<Longrightarrow>
         compatible_with_gctxt I \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D} \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
    proof-
      (* TODO: 'f *)
      fix I :: "'a gterm rel"
      let ?I = "(\<lambda>(x, y). Upair x y) ` I"
  
      assume 
        refl: "refl I" and 
        trans: "trans I" and 
        sym: "sym I" and
        compatible_with_gctxt: "compatible_with_gctxt I" and
        premise: "?I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D}"

      have var\<^sub>x_\<theta>_ground: "is_ground_term (Var var\<^sub>x \<cdot>t \<theta>)"
        by (metis context\<^sub>x(1) ground_term_is_ground ground_term_with_context3 ground_term_with_context_is_ground2(2) subst_apply_term_ctxt_apply_distrib term\<^sub>1_with_context_\<theta> var\<^sub>x)
        
      show "?I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      proof(cases "?I \<TTurnstile> premise\<^sub>G\<^sub>2'")
        case True
        then show ?thesis 
          by auto
      next
        let ?x =  "to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)"
        case False
        then have literal\<^sub>G\<^sub>2: "?I \<TTurnstile>l literal\<^sub>G\<^sub>2"
          using premise by blast

        then have "?I \<TTurnstile>l ?x\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> ?x\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
          unfolding ground_superpositionI(6)
          using compatible_with_gctxt compatible_with_gctxt_def sym by auto

        then have "?I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')"
          using term\<^sub>x_\<theta> term\<^sub>x_\<theta>'
          by argo

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
          using premise by fastforce

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
          using \<theta>'_grounding
          unfolding \<theta>'
          using congruence[OF refl trans sym compatible_with_gctxt replacement_grounding var\<^sub>x_\<theta>_ground]
          using \<open>(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')\<close> \<theta>' premise\<^sub>1_grounding' var\<^sub>x by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using ground_superpositionI(1) ground_superpositionI(5) premise\<^sub>1 by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using literal\<^sub>G\<^sub>2
         unfolding ground_superpositionI(6)
         by (smt (verit) False compatible_with_gctxt ground.G_entails_def ground.correctness_ground_superposition ground_superposition ground_superpositionI(1) ground_superpositionI(12) ground_superpositionI(2) ground_superpositionI(5) local.refl local.sym local.trans premise true_cls_union true_clss_insert union_commute union_mset_add_mset_right)
  
        then show ?thesis 
          by blast
      qed
 
    qed
  
    have var\<^sub>x_\<theta>: "\<theta> var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      using var\<^sub>x
      by simp

    have smaller': "((context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      unfolding context\<^sub>x(3) context\<^sub>x(1)[symmetric]
      unfolding term\<^sub>1_with_context_\<theta>
      by (simp add: ground_superpositionI(8) less\<^sub>t_less\<^sub>t\<^sub>G)

    then have xx: "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t \<theta> var\<^sub>x"
      unfolding var\<^sub>x_\<theta>
      using context_less[of "context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>" "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>" "term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"]
      by (metis Subterm_and_Context.ctxt_ctxt_compose context\<^sub>x(1) ground_term_with_context_is_ground1 ground_term_with_context_is_ground2(1) ground_term_with_context_is_ground2(2) replacement_grounding subst_compose_ctxt_compose_distrib term\<^sub>1_with_context_\<theta> testing2)

    have xy: "var\<^sub>x \<in> vars_literal (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1)"
      unfolding literal\<^sub>1 context\<^sub>x vars_literal_def vars_atom_def 
      using var\<^sub>x
      by(auto simp: subst_literal subst_atom)

    have "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>)"
      using literal\<^sub>1_grounding by force
    
    then have smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>"
      unfolding \<theta>'
      using literal_subst_less[of _ \<theta>, OF replacement_grounding xx _ xy]
      by blast

    have premise\<^sub>1'_\<theta>_grounding: "is_ground_clause (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1'_\<theta>
      by simp

    have smaller_premise\<^sub>1': "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>' \<preceq>\<^sub>c premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      unfolding \<theta>'
      using 
        clause_subst_less[of _ \<theta>, OF replacement_grounding xx premise\<^sub>1'_\<theta>_grounding]
        clause_subst_if_sth[of var\<^sub>x "premise\<^sub>1' \<cdot> \<rho>\<^sub>1"]
      by (metis (no_types, lifting) clause_subst_eq fun_upd_other reflclp_iff)

    from \<theta>'_grounding have "?D \<in> clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1')"
      unfolding clause_groundings_def clause_subst_compose[symmetric]
      by blast

    moreover have "?D \<prec>\<^sub>c\<^sub>G add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'"
      unfolding less\<^sub>c\<^sub>G_less\<^sub>c to_ground_clause_inverse[OF \<theta>'_grounding] to_clause_add_mset
      unfolding literal\<^sub>1_\<theta>[symmetric]  subst_clause_add_mset premise\<^sub>1'_\<theta>[symmetric]
      using smaller_literal'[OF smaller smaller_premise\<^sub>1']
      by simp

    moreover have "ground.G_entails (insert (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2') ?DD) {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      unfolding ground.G_entails_def
      using entails
      by blast

    ultimately show ?thesis
      unfolding ground.redundant_infer_def
      by auto
  qed

  have z: "(to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))) = 
             (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2))) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')"
    by (smt (verit) ground_superpositionI(9) ground_term_with_context3 to_atom_to_literal(1) to_atom_to_literal(2) to_clause_add_mset to_clause_inverse to_clause_plus to_term_to_atom)  

  have x: "\<lbrakk>
     ground.ground_superposition (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1') (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')
      (to_ground_clause
        (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')));

     \<not> ground.redundant_infer (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1']
           (to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))))\<rbrakk>
    \<Longrightarrow> \<exists>context\<^sub>1 term\<^sub>1. term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> is_Fun term\<^sub>1"
    unfolding z
    using special_case
    by blast

  obtain context\<^sub>1 term\<^sub>1 where 
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_\<theta> : "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<theta> : "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G" and
    term\<^sub>1_not_Var: "\<not> is_Var term\<^sub>1"
    using not_redundant ground_superposition
    unfolding premise\<^sub>1_\<theta> premise\<^sub>2_\<theta> conclusion_\<theta>\<^sub>G
    unfolding premise\<^sub>1 premise\<^sub>2
    apply auto
    unfolding ground.Red_I_def
    apply auto
    unfolding ground.G_Inf_def
     apply blast
    using x
    by blast
 
  obtain term\<^sub>2'_with_context where
    term\<^sub>2'_with_context: 
      "term\<^sub>2'_with_context \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      "term\<^sub>2'_with_context = (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>" 
    unfolding term\<^sub>2'_\<theta>[symmetric]  context\<^sub>1_\<theta>[symmetric]
    by force

  have term_term': "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta>"
    unfolding term\<^sub>1_\<theta> term\<^sub>2_\<theta>
    by(rule refl)

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  let ?conclusion' = "add_mset (?\<P> (Upair (term\<^sub>2'_with_context) (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
        (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  from conclusion_\<theta>\<^sub>G have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      term_subst_atom_subst
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit))+

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
      unfolding literal\<^sub>1 term\<^sub>1_with_context..
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
    show "?conclusion' =  add_mset
     ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1)))
     (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"
      using term\<^sub>2'_with_context(2) by blast
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
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
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

lemma inj': assumes "finite domain" "infinite image_subset"
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

lemma test: " (\<forall>x. is_Var (\<rho> x)) \<Longrightarrow> Var ` vars_term (term \<cdot>t \<rho>) = \<rho> ` (vars_term term)" 
  apply(cases "term")
   apply auto
     apply (metis term.disc(2) term.set_cases(2))
    apply (metis image_iff term.collapse(1) term.set_sel(3))
  apply (smt (verit, ccfv_SIG) UN_iff image_the_Var_image_subst_renaming_eq member_image_the_Var_image_subst vars_term_subst_apply_term)
  by (metis (no_types, lifting) UN_iff image_eqI term.collapse(1) term.set_sel(3) vars_term_subst)

lemma  (in first_order_superposition_calculus) test_atom: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_atom (atom \<cdot>a \<rho>) = \<rho> ` vars_atom atom"
  using test[OF assms]
  unfolding vars_atom_def subst_atom_def
  apply auto
   apply (smt (verit, del_insts) UN_iff image_iff uprod.set_map)
  by (smt (verit, ccfv_threshold) UN_I image_iff uprod.set_map)

lemma (in first_order_superposition_calculus) test_literal: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_literal (literal \<cdot>l \<rho>) = \<rho> ` vars_literal literal"
  using test_atom[OF assms]
  unfolding vars_literal_def subst_literal_def
  by (metis literal.map_sel(1) literal.map_sel(2))

lemma (in first_order_superposition_calculus) test_clause: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_clause (clause \<cdot> \<rho>) = \<rho> ` vars_clause clause"
  using test_literal[OF assms]
  unfolding vars_clause_def subst_clause_def
  apply auto
   apply (smt (verit, ccfv_threshold) UN_iff image_iff)
  using image_iff by fastforce 

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

lemma finite_vars_atom [simp]:
  "finite (vars_atom atom)"
  unfolding vars_atom_def
  by simp

lemma finite_vars_literal [simp]:
  "finite (vars_literal literal)"
  unfolding vars_literal_def
  by simp

lemma finite_vars_clause [simp]:
  "finite (vars_clause clause)"
  unfolding vars_clause_def
  by auto

context first_order_superposition_calculus
begin

lemmas term_renaming_exists = 
  renaming_exists[OF infinite_variable_universe finite_vars_term finite_vars_term]

lemmas atom_renaming_exists = 
  renaming_exists[OF infinite_variable_universe finite_vars_atom finite_vars_atom]

lemmas literal_renaming_exists = 
  renaming_exists[OF infinite_variable_universe finite_vars_literal finite_vars_literal]

lemmas clause_renaming_exists = 
  renaming_exists[OF infinite_variable_universe finite_vars_clause finite_vars_clause]

end

(* TODO: *)

lemma term_subst_if: "term \<cdot>t (\<lambda>var. if var \<in> vars_term term then x var else y var) = term \<cdot>t (\<lambda>var. x var)"
  by (smt (verit, ccfv_threshold) term_subst_eq)

lemma atom_subst_if: "atom \<cdot>a (\<lambda>var. if var \<in> vars_atom atom then x var else y var) = atom \<cdot>a (\<lambda>var. x var)"
  using term_subst_if
  unfolding subst_atom_def vars_atom_def
  by (smt (verit, ccfv_SIG) UN_I term_subst_eq uprod.map_cong0)

lemma literal_subst_if: "literal \<cdot>l (\<lambda>var. if var \<in> vars_literal literal then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  using atom_subst_if
  unfolding subst_literal_def vars_literal_def
  by(cases "literal") auto

lemma literal_subst_if': "literal \<in># clause
   \<Longrightarrow> literal \<cdot>l (\<lambda>var. if  \<exists>x\<in>#clause. var \<in> vars_literal x then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  unfolding vars_literal_def subst_literal_def
  apply(cases literal)
   apply auto
  by (smt (verit) UN_I literal.sel subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)+
  
(* TODO: generalize? *)
lemma clause_subst_if: "clause \<cdot> (\<lambda>var. if var \<in> vars_clause clause then x var else y var) = clause \<cdot> (\<lambda>var. x var)"
  unfolding subst_clause_def vars_clause_def 
  using literal_subst_if'[of _ clause x y]
  by simp

lemma term_subst_if'': "vars_term term\<^sub>1 \<subseteq> vars_term term\<^sub>2 \<Longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. x var)"
  apply(cases term\<^sub>1; cases term\<^sub>2)
     apply auto
   apply (smt (verit, ccfv_SIG) SUP_le_iff empty_iff singletonD subset_singletonD term_subst_eq)
  by (smt (verit, del_insts) Term.term.simps(18) subsetD term.distinct(1) term.inject(2) term.set_cases(2) term.set_intros(4) term_subst_eq)

lemma atom_subst_if'': "vars_atom atom\<^sub>1 \<subseteq> vars_atom atom\<^sub>2 \<Longrightarrow> atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) = atom\<^sub>1 \<cdot>a (\<lambda>var. x var)"
  using term_subst_if''
  unfolding subst_atom_def vars_atom_def
  by (smt (verit, del_insts) SUP_le_iff eval_same_vars_cong in_mono uprod.map_cong0)

lemma literal_subst_if'': "vars_literal literal\<^sub>1 \<subseteq> vars_literal literal\<^sub>2 \<Longrightarrow> literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) = literal\<^sub>1 \<cdot>l (\<lambda>var. x var)"
  using atom_subst_if''
  unfolding subst_literal_def vars_literal_def
  by(cases literal\<^sub>1) auto

lemma clause_subst_if''': "literal \<in># clause \<Longrightarrow> literal \<cdot>l (\<lambda>var. if var \<in> vars_clause clause then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  unfolding vars_literal_def subst_literal_def vars_clause_def
    apply(cases literal)
   apply auto
  apply (smt (verit, ccfv_SIG) UN_I subst_atom_def term_subst_eq upair_in_literal(1) uprod.map_cong0 vars_atom_def)
   by (smt (verit) UN_I subst_atom_def term_subst_eq upair_in_literal(2) uprod.map_cong0 vars_atom_def)

(* TODO: *)
lemma clause_subst_if': "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. x var)"
  unfolding subst_clause_def vars_clause_def 
  using clause_subst_if'''[of _ clause\<^sub>2 x y]
  by (metis (no_types, lifting) ext image_mset_cong2 mset_subsetD subset_mset.antisym_conv2 vars_clause_def)

lemma term_subst_if_2: "vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<Longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. y var)"
  apply(cases term\<^sub>1; cases term\<^sub>2)
     apply auto
   apply (smt (verit, ccfv_SIG) term_subst_eq)
  by (smt (verit, ccfv_SIG) UN_I disjoint_iff term_subst_eq)

lemma atom_subst_if_2: "vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<Longrightarrow> atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) = atom\<^sub>1 \<cdot>a (\<lambda>var. y var)"
  apply(cases atom\<^sub>1; cases atom\<^sub>2)
  using term_subst_if_2
  by (smt (verit, ccfv_SIG) IntI UN_I empty_iff subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)

lemma literal_subst_if_2: "vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<Longrightarrow> literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) = literal\<^sub>1 \<cdot>l (\<lambda>var. y var)"
   unfolding subst_literal_def vars_literal_def
   apply(cases literal\<^sub>1; cases literal\<^sub>2)
   apply auto
   using atom_subst_if_2 by blast+

abbreviation lift_to_atom 
  where "lift_to_atom P \<equiv> \<lambda>atom. \<forall>term \<in> set_uprod atom. P term"

abbreviation lift_to_literal 
  where "lift_to_literal P \<equiv> \<lambda>literal. P (atm_of literal)"

abbreviation lift_to_clause 
  where "lift_to_clause P \<equiv> \<lambda>clause.  \<forall>literal \<in># clause. P literal"

abbreviation lift_term_predicate_to_clause 
  where "lift_term_predicate_to_clause P \<equiv> lift_to_clause (lift_to_literal (lift_to_atom P))"

abbreviation lift_to_atom2 
  where "lift_to_atom2 P \<equiv> \<lambda>atom\<^sub>1 atom\<^sub>2. \<forall>term\<^sub>1 \<in> set_uprod atom\<^sub>1. \<forall>term\<^sub>2 \<in> set_uprod atom\<^sub>2. P term\<^sub>1 term\<^sub>2"

abbreviation lift_to_literal2
  where "lift_to_literal2 P \<equiv> \<lambda>literal\<^sub>1 literal\<^sub>2. P (atm_of literal\<^sub>1) (atm_of literal\<^sub>2)"

abbreviation lift_to_clause2 
  where "lift_to_clause2 P \<equiv> \<lambda>clause\<^sub>1 clause\<^sub>2.  \<forall>literal\<^sub>1 \<in># clause\<^sub>1. \<forall>literal\<^sub>2 \<in># clause\<^sub>2. P literal\<^sub>1 literal\<^sub>2"

abbreviation lift_term_predicate_to_clause2 
  where "lift_term_predicate_to_clause2 P \<equiv> lift_to_clause2 (lift_to_literal2 (lift_to_atom2 P))"


lemma clause_if_term: "\<forall>term. P term \<Longrightarrow> P' = lift_term_predicate_to_clause P \<Longrightarrow> P' clause"
  by auto

lemma clause2_if_term: "\<forall>term\<^sub>1 term\<^sub>2. P term\<^sub>1 term\<^sub>2 \<Longrightarrow> P' = lift_term_predicate_to_clause2 P \<Longrightarrow> P' clause\<^sub>1 clause\<^sub>2"
  by auto

lemma test': "\<forall> term\<^sub>1 term\<^sub>2. vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. y var)"
  using term_subst_if_2 by blast

lemma test_atom': "(lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)) atom\<^sub>1 atom\<^sub>2 =
                        (vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<longrightarrow>
                        atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) =
                        atom\<^sub>1 \<cdot>a y)"
  apply auto
  using atom_subst_if_2 apply blast
  using test' by blast+

lemma test_atom: "lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y) = (\<lambda>atom\<^sub>1 atom\<^sub>2.
                        vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<longrightarrow>
                        atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) =
                        atom\<^sub>1 \<cdot>a y)"
  using test_atom' 
  by fast

lemma test_literal': "(lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y))) literal\<^sub>1 literal\<^sub>2 = (
                        vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
                        literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
                        literal\<^sub>1 \<cdot>l y)"
  apply auto
  using literal_subst_if_2 apply blast
  using test' by blast+

lemma test_literal: "lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)) = (\<lambda>literal\<^sub>1 literal\<^sub>2.
                        vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
                        literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
                        literal\<^sub>1 \<cdot>l y)"
  using test_literal'
  by fast

lemma test_clause': 
  "(lift_to_clause2 (lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)))) (clause\<^sub>1 :: ('f, 'v) atom clause) (clause\<^sub>2 :: ('f, 'v) atom clause) = (
                        vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow>
                        clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
                        clause\<^sub>1 \<cdot> y)"
  apply(auto simp: test_literal')
  subgoal 
  proof-
    assume a: "lift_to_clause
      (\<lambda>literal\<^sub>1.
          lift_to_clause
           (\<lambda>literal\<^sub>2.
               vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
               literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
               literal\<^sub>1 \<cdot>l y)
           clause\<^sub>2)
      clause\<^sub>1" 
      "vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {}"

    then have "lift_to_clause
      (\<lambda>literal\<^sub>1.
          lift_to_clause
           (\<lambda>literal\<^sub>2.
               literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
               literal\<^sub>1 \<cdot>l y)
           clause\<^sub>2)
      clause\<^sub>1"
      apply auto
      by (smt (verit, ccfv_threshold) inf_assoc inf_bot_left inf_commute inf_sup_absorb multi_member_split vars_clause_add_mset)

    then have "lift_to_clause
     (\<lambda>literal.
              literal \<cdot>l (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
              literal \<cdot>l y)
     clause\<^sub>1"
      unfolding vars_clause_def
      apply auto
    proof-
      fix literal
      assume a': "lift_to_clause
         (\<lambda>literal.
             lift_to_clause
              (\<lambda>literala.
                  literal \<cdot>l (\<lambda>var. if var \<in> vars_literal literala then x var else y var) =
                  literal \<cdot>l y)
              clause\<^sub>2)
         clause\<^sub>1"
      "literal \<in># clause\<^sub>1"

      have "\<And>var. var \<in> vars_literal literal \<Longrightarrow> \<not>literal \<in># clause\<^sub>2"
        using a'(2) a(2)
        unfolding vars_clause_def
        by auto

      then have "\<And>var. var \<in> vars_literal literal \<Longrightarrow>  \<not> var \<in> \<Union> (vars_literal ` set_mset clause\<^sub>2)"
        apply auto
        by (metis IntI UN_I a'(2) a(2) emptyE vars_clause_def)

      then have "literal \<cdot>l (\<lambda>var. if var \<in> \<Union> (vars_literal ` set_mset clause\<^sub>2) then x var else y var) =
           literal \<cdot>l y "
        unfolding  subst_literal_def vars_literal_def
        apply auto
        by (smt (verit, ccfv_SIG) UN_I literal.expand literal.map_disc_iff literal.map_sel(1) literal.map_sel(2) subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)

      then show "literal \<cdot>l (\<lambda>var. if \<exists>x\<in>#clause\<^sub>2. var \<in> vars_literal x then x var else y var) =
           literal \<cdot>l y " 
        by auto
    qed  
    

    then show ?thesis
      unfolding vars_clause_def subst_clause_def
      by auto
  qed
  using literal_subst_if_2 by blast+

lemma test_clause: "lift_to_clause2 (lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y))) = (\<lambda>(clause\<^sub>1 :: ('f, 'v) atom clause) (clause\<^sub>2 :: ('f, 'v) atom clause).
                        vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow>
                        clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
                        clause\<^sub>1 \<cdot> y)"
  using test_clause' 
  by fast
 
lemma clause_subst_if_2: "vars_clause (clause\<^sub>1 :: ('f, 'v) atom clause)  \<inter> vars_clause (clause\<^sub>2 :: ('f, 'v) atom clause) = {} \<longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. y var)"
  apply(rule clause2_if_term[OF test', of "\<lambda>clause\<^sub>1 clause\<^sub>2. vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. y var)", of x y])
  by (simp add: test_clause)

lemma vars_clause_subset: "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> vars_clause clause\<^sub>1 \<subseteq> vars_clause clause\<^sub>2"
  by (metis Un_subset_iff order_refl subset_mset.add_diff_inverse vars_clause_plus)

lemma (in first_order_superposition_calculus_with_grounding) superposition_ground_instance': 
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

  obtain premise\<^sub>1 premise\<^sub>2 \<theta>\<^sub>1 \<theta>\<^sub>2 where
    premise\<^sub>1_\<theta>\<^sub>1: "premise\<^sub>1 \<cdot> \<theta>\<^sub>1 = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>\<^sub>2: "premise\<^sub>2 \<cdot> \<theta>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2" and
    select': 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<theta>\<^sub>1))) = select premise\<^sub>1 \<cdot> \<theta>\<^sub>1"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<theta>\<^sub>2))) = select premise\<^sub>2 \<cdot> \<theta>\<^sub>2" and
    premise\<^sub>1_in_premises: "premise\<^sub>1 \<in> premises" and
    premise\<^sub>2_in_premises: "premise\<^sub>2 \<in> premises"
     using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
     unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
     by (metis (no_types, lifting))

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    renaming: 
      "term_subst.is_renaming (\<rho>\<^sub>1 :: ('a, 'b) subst)" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "\<rho>\<^sub>1 ` vars_clause premise\<^sub>1 \<inter> \<rho>\<^sub>2 ` vars_clause premise\<^sub>2 = {}"
    using clause_renaming_exists[of premise\<^sub>1 premise\<^sub>2]. 

  (* TODO: *)
  then have vars_distinct: "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using test_clause[symmetric] term_subst_is_renaming_iff[of \<rho>\<^sub>1]  term_subst_is_renaming_iff[of \<rho>\<^sub>2]  
    by (smt (verit, del_insts) disjoint_iff imageI)

  from renaming obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
     \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
     \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  have select_subset: "select premise\<^sub>1 \<subseteq># premise\<^sub>1" "select premise\<^sub>2 \<subseteq># premise\<^sub>2"
    by (simp_all add: select_subset)

  then have a: "select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<subseteq># premise\<^sub>1 \<cdot> \<rho>\<^sub>1"  "select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<subseteq># premise\<^sub>2 \<cdot> \<rho>\<^sub>2"
    by (simp_all add: image_mset_subseteq_mono subst_clause_def)

  have "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<subseteq> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
    using vars_clause_subset[OF a(2)].

  then have b: "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<inter> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) = {}"
    using vars_distinct
    by blast

  obtain \<theta> where "\<theta> = (\<lambda>var. 
      if var \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) 
      then (\<rho>\<^sub>1_inv \<odot> \<theta>\<^sub>1) var 
      else (\<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2) var
    )"
    by simp

  then have 
    premise\<^sub>1_\<theta>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>"
    using premise\<^sub>1_\<theta>\<^sub>1 premise\<^sub>2_\<theta>\<^sub>2 select' 
       apply auto

    unfolding clause_subst_if clause_subst_if_2[rule_format, OF vars_distinct]  clause_subst_if_2[rule_format, OF vars_distinct]
    using \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv clause_subst_if_2[of "premise\<^sub>2 \<cdot> \<rho>\<^sub>2" "premise\<^sub>1 \<cdot> \<rho>\<^sub>2"]
       apply (metis (mono_tags, lifting) clause_subst_compose subst_clause_Var_ident)
      apply (metis (no_types) \<rho>\<^sub>2_inv clause_subst_compose clause_subst_if_2 inf_commute vars_distinct subst_clause_Var_ident)
    unfolding clause_subst_if'[OF a(1)]  clause_subst_if_2[rule_format, OF b]
    apply (metis (no_types, lifting) \<rho>\<^sub>1_inv clause_subst_compose select'(1) subst_clause_Var_ident)
  proof -
    assume a1: "premise\<^sub>2 \<cdot> \<theta>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2"
    assume a2: "to_clause (select\<^sub>G premise\<^sub>G\<^sub>2) = select premise\<^sub>2 \<cdot> \<theta>\<^sub>2"
    have "\<forall>m f. m \<cdot> f = m \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> f)"
      by (simp add: \<rho>\<^sub>2_inv)
    then show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> (\<lambda>b. if b \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) then (\<rho>\<^sub>1_inv \<odot> \<theta>\<^sub>1) b else (\<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2) b)))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2"
      using a2 a1 by (simp add: clause_subst_if_2 inf_commute vars_distinct)
  qed

  obtain conclusion where conclusion_\<theta>: "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>"
    by (metis ground_clause_is_ground subst_ground_clause)
   
  then have 
    premise\<^sub>1_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>2_grounding: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>1: "premise\<^sub>G\<^sub>1 = to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>2: "premise\<^sub>G\<^sub>2 = to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    apply (simp_all add: premise\<^sub>1_\<theta> premise\<^sub>2_\<theta>)
    by (smt ground_clause_is_ground to_clause_inverse)+

  have "clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2 \<subseteq> \<Union> (clause_groundings ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have " Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>))
  \<notin> ground.Red_I' (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
    using assms(3) ground.Red_I_of_subset
    unfolding \<iota>\<^sub>G  premise\<^sub>G\<^sub>1[symmetric] premise\<^sub>G\<^sub>2[symmetric] conclusion\<^sub>G[symmetric]
    by blast

 then obtain conclusion' where 
    superposition: "superposition premise\<^sub>1 premise\<^sub>2 conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings select\<^sub>G (Infer [premise\<^sub>1, premise\<^sub>2] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
     using superposition_ground_instance[OF 
        renaming(1, 2)
        vars_distinct
        premise\<^sub>1_grounding
        premise\<^sub>2_grounding
        conclusion_grounding 
        select 
        ground_superposition[unfolded premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G]
      ]
     by blast

   let ?\<iota> = "Infer [premise\<^sub>1, premise\<^sub>2] conclusion'"

   have "?\<iota> \<in> Inf_from premises"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises superposition
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings select\<^sub>G ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)


  ultimately  show ?thesis
    by blast
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
      superposition_ground_instance'
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
