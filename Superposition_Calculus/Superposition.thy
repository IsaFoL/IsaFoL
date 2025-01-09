theory Superposition
  imports
    Nonground_Order
    Ground_Superposition
    Nonground_Selection_Function
    Renaming
    Nonground_Typing

    Saturation_Framework.Lifting_to_Non_Ground_Calculi
begin

(* TODO: Remove Well_Quasi_Orders.Minimal_Elements from 
  Saturation_Framework.Lifting_to_Non_Ground_Calculi to get rid of Restricted_Predicates *)
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

section \<open>Nonground Layer\<close>

locale superposition_calculus =
  nonground_typing \<F> +
  nonground_equality_order less\<^sub>t +
  nonground_selection_function select
  for
    select :: "('f, 'v :: infinite) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" and
    \<F> :: "('f, 'ty) fun_types" +
  fixes
    tiebreakers :: "'f gatom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" 
  assumes
    tiebreakers: "\<And>C\<^sub>G. wellfounded_strict_order (tiebreakers C\<^sub>G)" and
    (* TODO: Move to locale assumption *)
    variables: "|UNIV :: 'ty set| \<le>o |UNIV :: 'v set|" and
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

interpretation term_order_notation.

sublocale tiebreakers: wellfounded_strict_order "tiebreakers C\<^sub>G"
  by (rule tiebreakers)

abbreviation typed_tiebreakers :: 
  "'f gatom clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where 
  "typed_tiebreakers C\<^sub>G C\<^sub>1 C\<^sub>2 \<equiv> tiebreakers C\<^sub>G (fst C\<^sub>1) (fst C\<^sub>2)"

sublocale typed_tiebreakers: wellfounded_strict_order "typed_tiebreakers C\<^sub>G"
proof unfold_locales
  show "transp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.transp 
    unfolding transp_def 
    by blast

  show "asymp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.asymp
    by (meson asympD asympI)

  show "wfp (typed_tiebreakers C\<^sub>G)"
    using tiebreakers.wfp
    by (meson wfp_if_convertible_to_wfp)
qed

inductive eq_resolution :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_resolutionI: 
   "D = add_mset l D' \<Longrightarrow>
    l = t !\<approx> t' \<Longrightarrow>
    welltyped_imgu \<V> t t' \<mu> \<Longrightarrow>
    select D = {#} \<and> is_maximal (l \<cdot>l \<mu>) (D \<cdot> \<mu>) \<or> is_maximal (l \<cdot>l \<mu>) (select D \<cdot> \<mu>) \<Longrightarrow>
    C = D' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution (D, \<V>) (C, \<V>)"

inductive eq_factoring :: "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool" where
  eq_factoringI: "
    D = add_mset l\<^sub>1 (add_mset l\<^sub>2 D') \<Longrightarrow>
    l\<^sub>1 = t\<^sub>1 \<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    select D = {#} \<Longrightarrow> 
    is_maximal (l\<^sub>1 \<cdot>l \<mu>) (D \<cdot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    welltyped_imgu \<V> t\<^sub>1 t\<^sub>2 \<mu> \<Longrightarrow>
    C = add_mset (t\<^sub>1 \<approx> t\<^sub>2') (add_mset (t\<^sub>1' !\<approx> t\<^sub>2') D') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring (D, \<V>) (C, \<V>)"

(* TODO: Get things like is_renaming out of the name scope *)
(* TODO: \<P> \<in> {Pos, Neg} *)
(* TODO: \<forall>x \<in> clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x *)
inductive superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  superpositionI:
   "term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    l\<^sub>1 = \<P> (Upair c\<^sub>1\<langle>t\<^sub>1\<rangle> t\<^sub>1') \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    (\<P> = Pos 
      \<and> select E = {#} 
      \<and> is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>)) \<or>
    (\<P> = Neg 
      \<and> (select E = {#} \<and> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) 
          \<or> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>))) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset (\<P> (Upair (c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow> 
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> { Infer [D] C | D C. eq_factoring D C }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> { Infer [D] C | D C. eq_resolution D C }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [D, E] C | D E C. superposition D E C}"

definition inferences :: "('f, 'v, 'ty) typed_clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v, 'ty) typed_clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {({#}, \<V>) | \<V>. infinite_variables_per_type \<V> }"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  pos_superpositionI: "
    term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> \<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    select E = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow> 
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    pos_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition D E C"
  shows "superposition D E C"
  using assms
proof (cases rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)
  then show ?thesis
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' Pos c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C]
    by blast
qed

inductive neg_superposition ::
  "('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> ('f, 'v, 'ty) typed_clause \<Rightarrow> bool"
where
  neg_superpositionI: "
    term.is_renaming \<rho>\<^sub>1 \<Longrightarrow>
    term.is_renaming \<rho>\<^sub>2 \<Longrightarrow>
    clause.vars (E \<cdot> \<rho>\<^sub>1) \<inter> clause.vars (D \<cdot> \<rho>\<^sub>2) = {} \<Longrightarrow>
    E = add_mset l\<^sub>1 E' \<Longrightarrow>
    D = add_mset l\<^sub>2 D' \<Longrightarrow>
    l\<^sub>1 = c\<^sub>1\<langle>t\<^sub>1\<rangle> !\<approx> t\<^sub>1' \<Longrightarrow>
    l\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>2' \<Longrightarrow>
    \<not> is_Var t\<^sub>1 \<Longrightarrow>
    welltyped_imgu \<V>\<^sub>3 (t\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<forall>x \<in> clause.vars (E \<cdot> \<rho>\<^sub>1). \<V>\<^sub>1 (inv \<rho>\<^sub>1 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    \<forall>x \<in> clause.vars (D \<cdot> \<rho>\<^sub>2). \<V>\<^sub>2 (inv \<rho>\<^sub>2 (Var x)) = \<V>\<^sub>3 x \<Longrightarrow>
    is_welltyped_on (clause.vars E) \<V>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
    is_welltyped_on (clause.vars D) \<V>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
    (\<And>\<tau> \<tau>'. typed \<V>\<^sub>2 t\<^sub>2 \<tau> \<Longrightarrow> typed \<V>\<^sub>2 t\<^sub>2' \<tau>' \<Longrightarrow> \<tau> = \<tau>') \<Longrightarrow>
    \<not> (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>c D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    select E = {#} \<and> 
      is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) (E \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<or> is_maximal (l\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<mu>) ((select E) \<cdot> \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal (l\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<mu>) (D \<cdot> \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    \<not> (c\<^sub>1\<langle>t\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<odot> \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<odot> \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<odot> \<mu>) \<Longrightarrow>
    C = add_mset ((c\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> !\<approx> (t\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (E' \<cdot> \<rho>\<^sub>1 + D' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>1 \<Longrightarrow>
    infinite_variables_per_type \<V>\<^sub>2 \<Longrightarrow>
    neg_superposition (D, \<V>\<^sub>2) (E, \<V>\<^sub>1) (C, \<V>\<^sub>3)"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition E D C"
  shows "superposition E D C"
  using assms
proof (cases E D C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)
  then show ?thesis
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' Neg c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C]
    by blast
qed

lemma superposition_iff_pos_or_neg:
  "superposition D E C \<longleftrightarrow> pos_superposition D E C \<or> neg_superposition D E C"
proof (rule iffI)
  assume "superposition D E C"
  thus "pos_superposition D E C \<or> neg_superposition D E C"
  proof (cases D E C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' \<P> c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C)
    then show ?thesis
      using
        pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C]
        neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 E D l\<^sub>1 E' l\<^sub>2 D' c\<^sub>1 t\<^sub>1 t\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu> \<V>\<^sub>3 \<V>\<^sub>1 \<V>\<^sub>2 C] 
      by blast
  qed
next
  assume "pos_superposition D E C \<or> neg_superposition D E C"
  thus "superposition D E C"
    using superposition_if_neg_superposition superposition_if_pos_superposition 
    by metis
qed

end

end
