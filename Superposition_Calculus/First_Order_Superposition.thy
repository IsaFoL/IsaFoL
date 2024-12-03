theory First_Order_Superposition
  imports
    Nonground_Order
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Select
    Renaming
    Nonground_Typing
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

(* TODO: Remove Restricted_Predicates all together? *)
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
  nonground_order less\<^sub>t +
  first_order_select select +
  nonground_typing typeof_fun
  for 
    select :: "('f, ('v :: infinite)) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
    typeof_fun :: "('f, 'ty) fun_types" + (* TODO: rename to \<F> *)
  fixes
    tiebreakers :: "'f gatom clause  \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" 
  assumes
    wellfounded_tiebreakers: 
      "\<And>clause\<^sub>G. wfP (tiebreakers clause\<^sub>G) \<and> 
               transp (tiebreakers clause\<^sub>G) \<and> 
               asymp (tiebreakers clause\<^sub>G)" and
  (* TODO/ Note: Was not needed without types \<rightarrow> Discuss *)
    function_symbols: "\<And>\<tau>. \<exists>f. typeof_fun f = ([], \<tau>)" and
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R" and
    variables: "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|"
begin

interpretation term_order_notation.

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
    by (meson wfp_if_convertible_to_wfp)

  show "transp (typed_tiebreakers clause\<^sub>G)"
    using wellfounded_tiebreakers
    by (smt (verit, ccfv_threshold) transpD transpI)

  show "asymp (typed_tiebreakers clause\<^sub>G)"
    using wellfounded_tiebreakers
    by (meson asympD asympI)
qed

definition is_merged_var_type_env where
  "is_merged_var_type_env \<V> X \<V>\<^sub>X \<rho>\<^sub>X Y \<V>\<^sub>Y \<rho>\<^sub>Y \<equiv>
    (\<forall>x \<in> X. welltyped \<V> (\<rho>\<^sub>X x) (\<V>\<^sub>X x)) \<and>
    (\<forall>y \<in> Y. welltyped \<V> (\<rho>\<^sub>Y y) (\<V>\<^sub>Y y))"

inductive eq_resolution :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_resolutionI: 
   "premise = add_mset literal premise' \<Longrightarrow>
    literal = term !\<approx> term' \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term, term' }} \<Longrightarrow>
    welltyped_imgu \<V> term term' \<mu> \<Longrightarrow>
    select premise = {#} \<and> is_maximal (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<or> 
      is_maximal (literal \<cdot>l \<mu>) ((select premise) \<cdot> \<mu>) \<Longrightarrow>
    conclusion = premise' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution (premise, \<V>) (conclusion, \<V>)"

inductive eq_factoring :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_factoringI: "
    premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise') \<Longrightarrow>
    literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1' \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    select premise = {#} \<Longrightarrow> 
    is_maximal (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term\<^sub>1, term\<^sub>2 }} \<Longrightarrow>
    welltyped_imgu \<V> term\<^sub>1 term\<^sub>2 \<mu> \<Longrightarrow>
    conclusion = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring (premise, \<V>) (conclusion, \<V>)"

(* TODO: Not sure if welltypedness for renaming is necessary, I think it's already implied *)
(* TODO: welltyped_on for imgu *)
(* TODO: weaken  all_types \<V>\<^sub>1 \<Longrightarrow> all_types \<V>\<^sub>2 *)
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
    welltyped_imgu \<V>\<^sub>3 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (premise\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (premise\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars premise\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars premise\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 term\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 term\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    (\<P> = Pos 
      \<and> select premise\<^sub>1 = {#} 
      \<and> is_strictly_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)) \<or>
    (\<P> = Neg 
      \<and> (select premise\<^sub>1 = {#} \<and> is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) 
          \<or> is_maximal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>))) \<Longrightarrow>
    select premise\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
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
    welltyped_imgu \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars P\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars P\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
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
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1']
    by blast
qed

(*lemma term_subst_is_renaming_iff_ex_inj_fun_on_vars:
  "term_subst.is_renaming \<rho> \<longleftrightarrow> (\<exists>f. inj f \<and> \<rho> = Var \<circ> f)"*)

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
    welltyped_imgu \<V>\<^sub>3 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>1 \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (P\<^sub>2 \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars P\<^sub>1) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars P\<^sub>2) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> 
      is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> is_maximal (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select P\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
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
    wt_D: "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using step
proof (cases "(D, \<V>)" "(C, \<V>)" rule: eq_resolution.cases)
  case (eq_resolutionI literal premise' "term" term' \<mu>)
  obtain \<tau> where \<tau>:
    "welltyped \<V> term \<tau>"
    "welltyped \<V> term' \<tau>"
    using wt_D
    unfolding 
      eq_resolutionI 
      clause.is_welltyped_add
    by auto

  then have "clause.is_welltyped \<V> (D  \<cdot> \<mu>)"
    using wt_D eq_resolutionI(4) clause.is_welltyped.subst_stability
    by (metis UNIV_I)
    
  then show ?thesis
    using clause.is_welltyped_add
    unfolding eq_resolutionI
    by auto
qed

(*TODO: Move *)
lemma typed_welltyped:
  assumes "typed \<V> term \<tau>" "welltyped \<V> term \<tau>'"
  shows "welltyped \<V> term \<tau>"
  using assms
  by (smt (verit, best) welltyped.simps typed.simps term.typed.right_unique right_uniqueD)

lemma welltyped_typed: 
  assumes "welltyped \<V> term \<tau>"
  shows "typed \<V> term \<tau>"
  using term.typed_if_welltyped[OF assms].

lemma eq_factoring_preserves_typing:
  assumes
    step: "eq_factoring (D, \<V>) (C, \<V>)" and
    wt_D: "clause.is_welltyped \<V> D"
  shows "clause.is_welltyped \<V> C"
  using step
proof (cases "(D, \<V>)" "(C, \<V>)" rule: eq_factoring.cases)
  case (eq_factoringI literal\<^sub>1 literal\<^sub>2 premise' term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>)
  
  have wt_D\<mu>: "clause.is_welltyped \<V> (D \<cdot> \<mu>)"
    using wt_D clause.is_welltyped.subst_stability eq_factoringI
    by (metis UNIV_I)

  show ?thesis
  proof-
    (* TODO *)
    have "\<And>\<tau> \<tau>'.
       \<lbrakk>\<forall>L\<in>#premise' \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). welltyped \<V> t \<tau>;
        welltyped \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau>;
        welltyped \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau>;
        welltyped \<V> (term\<^sub>2 \<cdot>t \<mu>) \<tau>';
        welltyped \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. welltyped \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau> \<and> welltyped \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>"
      by (metis UNIV_I local.eq_factoringI(8) term.welltyped.right_uniqueD 
          welltyped.subst_stability)

     moreover then have "\<And>\<tau> \<tau>'.
       \<lbrakk>\<forall>L\<in>#premise' \<cdot> \<mu>.
           \<exists>\<tau>. \<forall>t\<in>set_uprod (atm_of L). welltyped \<V> t \<tau>;
        welltyped \<V> (term\<^sub>1 \<cdot>t \<mu>) \<tau>;
        welltyped \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau>;
        welltyped \<V> (term\<^sub>2 \<cdot>t \<mu>) \<tau>';
        welltyped \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>'\<rbrakk>
       \<Longrightarrow> \<exists>\<tau>. welltyped \<V> (term\<^sub>1' \<cdot>t \<mu>) \<tau> \<and> welltyped \<V> (term\<^sub>2' \<cdot>t \<mu>) \<tau>"
       by (metis term.welltyped.right_uniqueD)

     ultimately show ?thesis
       using wt_D\<mu>
       unfolding eq_factoringI clause.add_subst subst_literal subst_atom literal_is_welltyped_iff
       by auto
   qed
qed

(* TODO: Naming!! *)
lemma superposition_preserves_typing:
  assumes
    step: "superposition (D, \<V>\<^sub>2) (C, \<V>\<^sub>1) (E, \<V>\<^sub>3)" and
    wt_C: "clause.is_welltyped \<V>\<^sub>1 C" and
    wt_D: "clause.is_welltyped \<V>\<^sub>2 D"
  shows "clause.is_welltyped \<V>\<^sub>3 E"
  using step
proof (cases "(D, \<V>\<^sub>2)" "(C, \<V>\<^sub>1)" "(E, \<V>\<^sub>3)" rule: superposition.cases)
  case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' \<P> context\<^sub>1 term\<^sub>1 term\<^sub>1' term\<^sub>2 
         term\<^sub>2' \<mu>)

  have welltyped_\<mu>: "is_welltyped \<V>\<^sub>3 \<mu>"
    using superpositionI(11)
    by blast

  have "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1)"
    using wt_C clause.is_welltyped.typed_renaming[OF superpositionI(1, 12)] 
    by blast

  then have wt_C\<mu>: "clause.is_welltyped \<V>\<^sub>3 (C \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>)"
    by (metis UNIV_I clause.is_welltyped.subst_stability welltyped_\<mu>)
   
  have "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2)"
    using wt_D  clause.is_welltyped.typed_renaming[OF superpositionI(2, 13)] 
    by blast    

  then have wt_D\<mu>: "clause.is_welltyped \<V>\<^sub>3 (D \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>)"
    by (metis UNIV_I clause.is_welltyped.subst_stability welltyped_\<mu>)

  have imgu: "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>"
    using term_subst.is_imgu_unifies'[OF superpositionI(10)].

  show ?thesis
     (* TODO *)
    using literal_cases[OF superpositionI(6)] wt_C\<mu> wt_D\<mu>
    apply cases
    apply (clause_simp simp: superpositionI imgu)
    apply (smt (verit, best) atom_is_welltyped_iff clause.is_welltyped_add clause.is_welltyped_plus
        literal.sel(1) literal_is_welltyped_iff welltyped.context_compatible)
    by (smt (verit) atom_is_welltyped_iff clause.is_welltyped_add clause.is_welltyped_plus
        literal.sel(1,2) literal_is_welltyped_iff welltyped.context_compatible)
qed

end

end
