theory First_Order_Superposition
  imports
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Select
    First_Order_Ordering
    First_Order_Type_System
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

(* Hide as much of Restricted_Predicates.wfp_on as possible *)
hide_fact
  Restricted_Predicates.wfp_on_imp_minimal
  Restricted_Predicates.wfp_on_imp_inductive_on
  Restricted_Predicates.inductive_on_imp_wfp_on
  Restricted_Predicates.wfp_on_iff_inductive_on
  Restricted_Predicates.wfp_on_iff_minimal
  Restricted_Predicates.wfp_on_imp_has_min_elt
  Restricted_Predicates.wfp_on_induct
  Restricted_Predicates.wfp_on_UNIV
  Restricted_Predicates.wfp_less
  Restricted_Predicates.wfp_on_measure_on
  Restricted_Predicates.wfp_on_mono
  Restricted_Predicates.wfp_on_subset
  Restricted_Predicates.wfp_on_restrict_to
  Restricted_Predicates.wfp_on_imp_irreflp_on
  Restricted_Predicates.accessible_on_imp_wfp_on
  Restricted_Predicates.wfp_on_tranclp_imp_wfp_on
  Restricted_Predicates.wfp_on_imp_accessible_on
  Restricted_Predicates.wfp_on_accessible_on_iff
  Restricted_Predicates.wfp_on_restrict_to_tranclp
  Restricted_Predicates.wfp_on_restrict_to_tranclp'
  Restricted_Predicates.wfp_on_restrict_to_tranclp_wfp_on_conv

section \<open>First-Order Layer\<close>

locale first_order_superposition_calculus =
  first_order_select select +
  first_order_ordering less\<^sub>t
  for 
    select :: "('f, ('v :: infinite)) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  fixes
    tiebreakers :: "'f gatom clause  \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" and
    typeof_fun :: "('f, 'ty) fun_types"
  assumes
    wellfounded_tiebreakers: 
      "\<And>clause\<^sub>G. wfP (tiebreakers clause\<^sub>G) \<and> 
               transp (tiebreakers clause\<^sub>G) \<and> 
               asymp (tiebreakers clause\<^sub>G)" and
    function_symbols: "\<And>\<tau>. \<exists>f. typeof_fun f = ([], \<tau>)" and
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R" and
    variables: "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|"
begin

abbreviation typed_tiebreakers :: 
      "'f gatom clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where 
    "typed_tiebreakers clause\<^sub>G clause\<^sub>1 clause\<^sub>2 \<equiv> tiebreakers clause\<^sub>G (fst clause\<^sub>1) (fst clause\<^sub>2)"

lemma wellfounded_typed_tiebreakers: 
      "wfP (typed_tiebreakers clause\<^sub>G) \<and> 
       transp (typed_tiebreakers clause\<^sub>G) \<and>
      asymp (typed_tiebreakers clause\<^sub>G)"
proof(intro conjI)

  show "wfp (typed_tiebreakers clause\<^sub>G)"
    using wellfounded_tiebreakers
    by (meson wfP_if_convertible_to_wfP)

  show "transp (typed_tiebreakers clause\<^sub>G)"
    using wellfounded_tiebreakers
    by (smt (verit, ccfv_threshold) transpD transpI)

  show "asymp (typed_tiebreakers clause\<^sub>G)"
    using wellfounded_tiebreakers
    by (meson asympD asympI)
qed

definition is_merged_var_type_env where
  "is_merged_var_type_env \<V> X \<V>\<^sub>X \<rho>\<^sub>X Y \<V>\<^sub>Y \<rho>\<^sub>Y \<equiv>
    (\<forall>x \<in> X. welltyped typeof_fun \<V> (\<rho>\<^sub>X x) (\<V>\<^sub>X x)) \<and>
    (\<forall>y \<in> Y. welltyped typeof_fun \<V> (\<rho>\<^sub>Y y) (\<V>\<^sub>Y y))"

inductive eq_resolution :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_resolutionI: 
   "premise = add_mset literal premise' \<Longrightarrow>
    literal = term !\<approx> term' \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term, term' }} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V> term term' \<mu> \<Longrightarrow>
    select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<or> 
      is_maximal\<^sub>l (literal \<cdot>l \<mu>) ((select premise) \<cdot> \<mu>) \<Longrightarrow>
    conclusion = premise' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution (premise, \<V>) (conclusion, \<V>)"

inductive eq_factoring :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_factoringI: "
    premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise') \<Longrightarrow>
    literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1' \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    select premise = {#} \<Longrightarrow> 
    is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term\<^sub>1, term\<^sub>2 }} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V> term\<^sub>1 term\<^sub>2 \<mu> \<Longrightarrow>
    conclusion = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring (premise, \<V>) (conclusion, \<V>)"

inductive superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  superpositionI:
   "term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter>  clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1' \<Longrightarrow>
    premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    literal\<^sub>1 = \<P> (Upair context\<^sub>1\<langle>term\<^sub>1\<rangle> term\<^sub>1') \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    \<not> is_Var term\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars premise\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. has_type typeof_fun \<V>\<^sub>2 term\<^sub>2 \<tau> \<Longrightarrow> has_type typeof_fun \<V>\<^sub>2 term\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos 
      \<and> select premise\<^sub>1 = {#} 
      \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg 
      \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>))) \<Longrightarrow>
    select premise\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    conclusion = add_mset (\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    all_types \<V>\<^sub>1 \<Longrightarrow> all_types \<V>\<^sub>2 \<Longrightarrow>
    superposition (premise\<^sub>2, \<V>\<^sub>2) (premise\<^sub>1, \<V>\<^sub>1) (conclusion, \<V>\<^sub>3)"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. eq_factoring premise conclusion }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. eq_resolution premise conclusion }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [premise\<^sub>2, premise\<^sub>1] conclusion 
    |  premise\<^sub>2 premise\<^sub>1 conclusion. superposition premise\<^sub>2 premise\<^sub>1 conclusion}"

definition inferences :: "('f, 'v, 'ty) typed_clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {({#}, \<V>) | \<V>. all_types \<V> }"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = s\<^sub>1\<langle>u\<^sub>1\<rangle> \<approx> s\<^sub>1' \<Longrightarrow>
    L\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. has_type typeof_fun \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> has_type typeof_fun \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    all_types \<V>\<^sub>1 \<Longrightarrow> all_types \<V>\<^sub>2 \<Longrightarrow>
    pos_superposition (P\<^sub>2, \<V>\<^sub>2) (P\<^sub>1, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
  using assms
proof (cases rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)
  then show ?thesis
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2]
    by blast
qed

inductive neg_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term_subst.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term_subst.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    L\<^sub>1 = s\<^sub>1\<langle>u\<^sub>1\<rangle> !\<approx> s\<^sub>1' \<Longrightarrow>
    L\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var u\<^sub>1 \<Longrightarrow>
    term_subst.is_imgu \<mu> {{u\<^sub>1 \<cdot>t \<rho>\<^sub>1, t\<^sub>2 \<cdot>t \<rho>\<^sub>2}} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (the_inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (the_inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>1) typeof_fun \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    welltyped\<^sub>\<sigma>_on (clause.vars P\<^sub>2) typeof_fun \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. has_type typeof_fun \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> has_type typeof_fun \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> 
      is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select P\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    all_types \<V>\<^sub>1 \<Longrightarrow> all_types \<V>\<^sub>2 \<Longrightarrow>
    neg_superposition (P\<^sub>2, \<V>\<^sub>2) (P\<^sub>1, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition  P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
  using assms
proof (cases P\<^sub>2 P\<^sub>1 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)
  then show ?thesis
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2']
    by blast
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>2 P\<^sub>1 C \<longleftrightarrow> pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2  P\<^sub>1 C"
proof (rule iffI)
  assume "superposition P\<^sub>2 P\<^sub>1 C"
  thus "pos_superposition  P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  proof (cases P\<^sub>2 P\<^sub>1 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 premise\<^sub>1 premise\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' \<P> context\<^sub>1 
          term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>)
    then show ?thesis
      using
        pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 premise\<^sub>1 premise\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' context\<^sub>1 
                              term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>]
        neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 premise\<^sub>1 premise\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' context\<^sub>1 
                              term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>] 
      by blast
  qed
next
  assume "pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  thus "superposition P\<^sub>2 P\<^sub>1 C"
    using superposition_if_neg_superposition superposition_if_pos_superposition by metis
qed

lemma eq_resolution_preserves_typing:
  assumes
    step: "eq_resolution (D, \<V>) (C, \<V>)" and
    wt_D: "welltyped\<^sub>c typeof_fun \<V> D"
  shows "welltyped\<^sub>c typeof_fun \<V> C"
  using step
proof (cases "(D, \<V>)" "(C, \<V>)" rule: eq_resolution.cases)
  case (eq_resolutionI literal premise' "term" term' \<mu>)
  obtain \<tau> where \<tau>:
    "welltyped typeof_fun \<V> term \<tau>"
    "welltyped typeof_fun \<V> term' \<tau>"
    using wt_D
    unfolding 
      eq_resolutionI 
      welltyped\<^sub>c_add_mset 
      welltyped\<^sub>l_def 
      welltyped\<^sub>a_def
    by clause_simp

  then have "welltyped\<^sub>c typeof_fun \<V> (D  \<cdot> \<mu>)"
    using wt_D welltyped\<^sub>\<sigma>_welltyped\<^sub>c eq_resolutionI(4)
    by blast
    
  then show ?thesis
    unfolding eq_resolutionI subst_clause_add_mset welltyped\<^sub>c_add_mset
    by clause_simp
qed

lemma has_type_welltyped:
  assumes "has_type typeof_fun \<V> term \<tau>" "welltyped typeof_fun \<V> term \<tau>'"
  shows "welltyped typeof_fun \<V> term \<tau>"
  using assms
  by (smt (verit, best) welltyped.simps has_type.simps has_type_right_unique right_uniqueD)

lemma welltyped_has_type: 
  assumes "welltyped typeof_fun \<V> term \<tau>"
  shows "has_type typeof_fun \<V> term \<tau>"
  using assms welltyped.cases has_type.simps by fastforce

lemma eq_factoring_preserves_typing:
  assumes
    step: "eq_factoring (D, \<V>) (C, \<V>)" and
    wt_D: "welltyped\<^sub>c typeof_fun \<V> D"
  shows "welltyped\<^sub>c typeof_fun \<V> C"
  using step
proof (cases "(D, \<V>)" "(C, \<V>)" rule: eq_factoring.cases)
  case (eq_factoringI literal\<^sub>1 literal\<^sub>2 premise' term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>)
  
  have wt_D\<mu>: "welltyped\<^sub>c typeof_fun \<V> (D \<cdot> \<mu>)"
    using wt_D welltyped\<^sub>\<sigma>_welltyped\<^sub>c eq_factoringI
    by blast

  show ?thesis
  proof-
    have "\<And>\<tau> \<tau>'.
       \<lbrakk>\<forall>L\<in>#premise' \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). First_Order_Type_System.welltyped typeof_fun \<V> t \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2 \<cdot>t \<mu>) \<tau>';
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau> \<and>
               First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>"
       by (metis welltyped_right_unique eq_factoringI(8) right_uniqueD welltyped\<^sub>\<sigma>_welltyped)

     moreover have "\<And>\<tau> \<tau>'.
       \<lbrakk>\<forall>L\<in>#premise' \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). First_Order_Type_System.welltyped typeof_fun \<V> t \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau>;
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2 \<cdot>t \<mu>) \<tau>';
        First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau> \<and>
               First_Order_Type_System.welltyped typeof_fun \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>"
       by (metis welltyped_right_unique eq_factoringI(8) right_uniqueD welltyped\<^sub>\<sigma>_welltyped)

     ultimately show ?thesis
       using wt_D\<mu>
       unfolding welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def eq_factoringI subst_clause_add_mset 
         subst_literal subst_atom
       by auto
   qed
qed

lemma superposition_preserves_typing:
  assumes
    step: "superposition (D, \<V>\<^sub>2) (C, \<V>\<^sub>1) (E, \<V>\<^sub>3)" and
    wt_C: "welltyped\<^sub>c typeof_fun \<V>\<^sub>1 C" and
    wt_D: "welltyped\<^sub>c typeof_fun \<V>\<^sub>2 D"
  shows "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 E"
  using step
proof (cases "(D, \<V>\<^sub>2)" "(C, \<V>\<^sub>1)" "(E, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' \<P> context\<^sub>1 term\<^sub>1 term\<^sub>1' term\<^sub>2 
         term\<^sub>2' \<mu>)

  have welltyped_\<mu>: "welltyped\<^sub>\<sigma> typeof_fun \<V>\<^sub>3 \<mu>"
    using superpositionI(11)
    by blast

  have "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1)"
    using wt_C welltyped\<^sub>c_renaming_weaker[OF superpositionI(1, 12)] 
    by blast

  then have wt_C\<mu>: "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
    using welltyped\<^sub>\<sigma>_welltyped\<^sub>c[OF welltyped_\<mu>]
    by blast

  have "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using wt_D welltyped\<^sub>c_renaming_weaker[OF superpositionI(2, 13)]
    by blast    

  then have wt_D\<mu>: "welltyped\<^sub>c typeof_fun \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
    using welltyped\<^sub>\<sigma>_welltyped\<^sub>c[OF welltyped_\<mu>]
    by blast

  note imgu = term_subst.subst_imgu_eq_subst_imgu[OF superpositionI(10)]

  show ?thesis
    using literal_cases[OF superpositionI(6)] wt_C\<mu> wt_D\<mu>
    by cases (clause_simp simp: superpositionI imgu)
qed

end

end
