theory First_Order_Superposition
  imports
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
    Ground_Superposition
    First_Order_Select
    First_Order_Ordering
    Renaming
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

section \<open>First-Order Layer\<close>

definition clause_groundings ::
  "('f, 'v) atom clause \<Rightarrow> 'f ground_atom clause set" where
  "clause_groundings clause = { to_ground_clause (clause \<cdot> \<theta>) | \<theta>. is_ground_clause (clause \<cdot> \<theta>) }"

locale first_order_superposition_calculus =
  first_order_select select +
  first_order_ordering less\<^sub>t +
  renaming "UNIV :: 'v set"
  for 
    select :: "('f, 'v) select" and
    less\<^sub>t :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) +
  fixes
    tiebreakers :: "'f gatom clause  \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool"
  assumes
    wellfounded_tiebreakers: 
      "\<And>term\<^sub>G. wfP (tiebreakers term\<^sub>G) \<and> 
               transp (tiebreakers term\<^sub>G) \<and> 
               asymp (tiebreakers term\<^sub>G)" and
    (* TODO: Use theorem from CeTA *)
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

inductive equality_resolution :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  equality_resolutionI: 
   "premise = add_mset literal premise' \<Longrightarrow>
    literal = term !\<approx> term' \<Longrightarrow>
    term_subst.is_imgu \<mu> {{ term, term' }} \<Longrightarrow>
    select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<or> 
      is_maximal\<^sub>l literal (select premise) \<Longrightarrow>
    conclusion = premise' \<cdot> \<mu> \<Longrightarrow>
    equality_resolution premise conclusion"

inductive equality_factoring :: "('f, 'v) atom clause \<Rightarrow> ('f, 'v) atom clause \<Rightarrow> bool" where
  equality_factoringI: "
    premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise') \<Longrightarrow>
    literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1' \<Longrightarrow>
    literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2' \<Longrightarrow>
    select premise = {#} \<Longrightarrow> 
    is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<mu>) (premise \<cdot> \<mu>) \<Longrightarrow>
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
          \<or> is_maximal\<^sub>l literal\<^sub>1 (select premise\<^sub>1))) \<Longrightarrow>
    select premise\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    conclusion = add_mset (\<P> (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
          (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    superposition premise\<^sub>2 premise\<^sub>1 conclusion"

abbreviation equality_factoring_inferences where
  "equality_factoring_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. equality_factoring premise conclusion }"

abbreviation equality_resolution_inferences where
  "equality_resolution_inferences \<equiv> 
    { Infer [premise] conclusion | premise conclusion. equality_resolution premise conclusion }"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> { Infer [premise\<^sub>2, premise\<^sub>1] conclusion 
    | premise\<^sub>1 premise\<^sub>2 conclusion. superposition premise\<^sub>2 premise\<^sub>1 conclusion }"

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
    pos_superposition P\<^sub>2 P\<^sub>1 C"

lemma superposition_if_pos_superposition:
  assumes "pos_superposition P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
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
    select P\<^sub>1 = {#} \<and> is_maximal\<^sub>l (L\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<mu>) (P\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<mu>) \<or> is_maximal\<^sub>l L\<^sub>1 (select P\<^sub>1) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal\<^sub>l  (L\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<mu>) (P\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<mu>) \<Longrightarrow>
    \<not> (s\<^sub>1\<langle>u\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu> \<preceq>\<^sub>t s\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<mu>) \<Longrightarrow>
    \<not> (t\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu> \<preceq>\<^sub>t t\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<mu>) \<Longrightarrow>
    C = add_mset (Neg (Upair (s\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>t\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>  (s\<^sub>1' \<cdot>t \<rho>\<^sub>1))) (P\<^sub>1' \<cdot> \<rho>\<^sub>1 + P\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<mu> \<Longrightarrow>
    neg_superposition P\<^sub>2 P\<^sub>1 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
  using assms
proof (cases P\<^sub>2 P\<^sub>1 C rule: neg_superposition.cases)
  case (neg_superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
  then show ?thesis
    using superpositionI
    by simp
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>2 P\<^sub>1 C \<longleftrightarrow> pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
proof (rule iffI)
  assume "superposition P\<^sub>2 P\<^sub>1 C"
  thus "pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  proof (cases P\<^sub>2 P\<^sub>1 C rule: superposition.cases)
    case (superpositionI \<rho>\<^sub>1 \<rho>\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>)
    then show ?thesis      
      using pos_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      using neg_superpositionI[of \<rho>\<^sub>1 \<rho>\<^sub>2 P\<^sub>1 P\<^sub>2 L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s\<^sub>1 u\<^sub>1 s\<^sub>1' t\<^sub>2 t\<^sub>2' \<mu>]
      by blast
  qed
next
  assume "pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  thus "superposition P\<^sub>2 P\<^sub>1 C"
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

end

end
