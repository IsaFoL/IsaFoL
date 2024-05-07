theory First_Order_Superposition
  imports
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Select
    First_Order_Ordering
    Renaming
    First_Order_Type_System
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

section \<open>First-Order Layer\<close>

type_synonym ('f, 'v, 'ty) typed_clause = "('f, 'v) atom clause \<times> ('v, 'ty) var_types"

locale first_order_superposition_calculus =
  first_order_select select +
  first_order_ordering less\<^sub>t +
  renaming "UNIV :: 'v set"
  for 
    select :: "('f, 'v) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  fixes
    tiebreakers :: "'f gatom clause  \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" and
    typeof_fun :: "('f, 'ty) fun_types"
  assumes
    wellfounded_tiebreakers: 
      "\<And>clause\<^sub>G. wfP (tiebreakers clause\<^sub>G) \<and> 
               transp (tiebreakers clause\<^sub>G) \<and> 
               asymp (tiebreakers clause\<^sub>G)" and
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

inductive eq_resolution :: "('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_resolutionI: 
   "premise = add_mset literal premise' \<Longrightarrow>
    literal = term !\<approx> term' \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term, term' }} \<Longrightarrow>
    welltyped_imgu' typeof_fun \<V> term term' \<mu> \<Longrightarrow>
    select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<or> 
      is_maximal\<^sub>l (literal \<cdot>l \<mu>) ((select premise) \<cdot> \<mu>) \<Longrightarrow>
    conclusion = premise' \<cdot> \<mu> \<Longrightarrow>
    eq_resolution \<V> premise conclusion"

inductive eq_factoring :: "('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  eq_factoringI: "
    premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise') \<Longrightarrow>
    literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1' \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    select premise = {#} \<Longrightarrow> 
    is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<mu>) \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term\<^sub>1, term\<^sub>2 }} \<Longrightarrow>
    welltyped_imgu typeof_fun \<V> term\<^sub>1 term\<^sub>2 \<mu> \<Longrightarrow>
    (welltyped\<^sub>c typeof_fun \<V> premise \<Longrightarrow> \<exists>\<tau>. has_type typeof_fun \<V> term\<^sub>1 \<tau> \<and> has_type typeof_fun \<V> term\<^sub>2 \<tau>) \<Longrightarrow>
    conclusion = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<mu> \<Longrightarrow>
    eq_factoring \<V> premise conclusion"

(* TODO *)
inductive superposition ::
  "('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
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
    welltyped_imgu typeof_fun \<V>\<^sub>1 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    welltyped_imgu typeof_fun \<V>\<^sub>2 (term\<^sub>1 \<cdot>t \<rho>\<^sub>1) (term\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
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
    superposition \<V>\<^sub>2 premise\<^sub>2 \<V>\<^sub>1 premise\<^sub>1 conclusion"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> 
    { Infer [premise] conclusion | \<V> premise conclusion. eq_factoring \<V> premise conclusion }"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> 
    { Infer [premise] conclusion | \<V> premise conclusion. eq_resolution \<V> premise conclusion }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [premise\<^sub>2, premise\<^sub>1] conclusion 
    |  \<V>\<^sub>2 premise\<^sub>2 \<V>\<^sub>1 premise\<^sub>1 conclusion. superposition \<V>\<^sub>2 premise\<^sub>2 \<V>\<^sub>1 premise\<^sub>1 conclusion}"

definition inferences :: "('f, 'v) atom clause inference set" where
  "inferences \<equiv> superposition_inferences \<union> eq_resolution_inferences \<union> eq_factoring_inferences"

abbreviation bottom\<^sub>F :: "('f, 'v) atom clause set" ("\<bottom>\<^sub>F") where
  "bottom\<^sub>F \<equiv> {{#}}"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive pos_superposition ::
  "('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
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
    welltyped_imgu typeof_fun \<V>\<^sub>1 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    welltyped_imgu typeof_fun \<V>\<^sub>2 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset ((s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> \<approx> (s\<^sub>1' \<cdot>t \<rho>\<^sub>1)) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    pos_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  shows "superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  using assms
proof (cases rule: pos_superposition.cases)
  case (pos_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2]
    by blast
qed

inductive neg_superposition ::
  "('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
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
    welltyped_imgu typeof_fun \<V>\<^sub>1 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    welltyped_imgu typeof_fun \<V>\<^sub>2 (u\<^sub>1 \<cdot>t \<rho>\<^sub>1) (t\<^sub>2 \<cdot>t \<rho>\<^sub>2) \<mu> \<Longrightarrow>
    \<not> (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu> \<preceq>\<^sub>c P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> 
      is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) ((select P\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition  \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  shows "superposition  \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  using assms
proof (cases \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by simp
qed

lemma superposition_iff_pos_or_neg:
  "superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C \<longleftrightarrow> pos_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C \<or> neg_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
proof (rule iffI)
  assume "superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  thus "pos_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C \<or> neg_superposition \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  proof (cases \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' \<P> context\<^sub>1 term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>)
    then show ?thesis 
      using 
        pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' context\<^sub>1 term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2']
        neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 literal\<^sub>1 premise\<^sub>1' literal\<^sub>2 premise\<^sub>2' context\<^sub>1 term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2'] 
      by blast
  qed
next
  assume "pos_superposition  \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C \<or> neg_superposition  \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
  thus "superposition  \<V>\<^sub>2 P\<^sub>2 \<V>\<^sub>1 P\<^sub>1 C"
    using superposition_if_neg_superposition superposition_if_pos_superposition by metis
qed

lemmas term_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_term finite_vars_term]

lemmas atom_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_atom finite_vars_atom]

lemmas literal_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_literal finite_vars_literal]

lemmas clause_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_clause finite_vars_clause]

(* TODO: abbreviations without typeof_fun typeof_var *)
lemma eq_resolution_preserves_typing:
  assumes
    step: "eq_resolution \<V> D C" and
    wt_D: "welltyped\<^sub>c typeof_fun \<V> D"
  shows "welltyped\<^sub>c typeof_fun \<V> C"
  using step
proof (cases \<V> D C rule: eq_resolution.cases)
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
    by auto

  then have "welltyped\<^sub>c typeof_fun \<V> (D  \<cdot> \<mu>)"
    using wt_D welltyped\<^sub>\<sigma>_welltyped\<^sub>c eq_resolutionI(4)
    by blast

  then show ?thesis
    unfolding eq_resolutionI subst_clause_add_mset welltyped\<^sub>c_add_mset
    by blast
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
    step: "eq_factoring \<V> D C" and
    wt_D: "welltyped\<^sub>c typeof_fun \<V> D"
  shows "welltyped\<^sub>c typeof_fun \<V> C"
  using step
proof (cases \<V> D C rule: eq_factoring.cases)
  case (eq_factoringI literal\<^sub>1 literal\<^sub>2 premise' term\<^sub>1 term\<^sub>1' term\<^sub>2 term\<^sub>2' \<mu>)
  
  obtain \<tau> where \<tau>:
    "has_type typeof_fun \<V> term\<^sub>1 \<tau>"
    "has_type typeof_fun \<V> term\<^sub>2 \<tau>"
    using eq_factoringI(9)[OF wt_D]
    by blast

  then have "welltyped typeof_fun \<V> term\<^sub>1 \<tau>" "welltyped typeof_fun \<V> term\<^sub>2 \<tau>"
    using wt_D has_type_welltyped
    unfolding welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def eq_factoringI
    by auto

  moreover then have "welltyped\<^sub>c typeof_fun \<V> (D  \<cdot> \<mu>)"
    using wt_D welltyped\<^sub>\<sigma>_welltyped\<^sub>c eq_factoringI
    by blast

  ultimately show ?thesis
    unfolding welltyped\<^sub>c_def welltyped\<^sub>l_def welltyped\<^sub>a_def eq_factoringI subst_clause_add_mset subst_literal subst_atom
    (* TODO: *)
    apply auto
    by (metis First_Order_Type_System.welltyped_right_unique local.eq_factoringI(8) right_uniqueD welltyped\<^sub>\<sigma>_welltyped)+
qed

end

end
