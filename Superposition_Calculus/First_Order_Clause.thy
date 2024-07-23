theory First_Order_Clause
  imports 
    Ground_Clause
    Abstract_Substitution.Substitution_First_Order_Term
    Abstract_Substitution.Variable_Substitution
    Clausal_Calculus_Extra
    Multiset_Extra
    Term_Rewrite_System
    Term_Ordering_Lifting
    "HOL-Eisbach.Eisbach"
begin

(* TODO: split up file*)

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>First_Order_Terms And Abstract_Substitution\<close>

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_apply_ctxt (infixl "\<cdot>t\<^sub>c" 67)
notation subst_compose (infixl "\<odot>" 75)

lemmas clause_simp_term =
  subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply literal.sel

named_theorems clause_simp
named_theorems clause_intro

lemma ball_set_uprod [clause_simp]: "(\<forall>t\<in>set_uprod (Upair t\<^sub>1 t\<^sub>2). P t) \<longleftrightarrow> P t\<^sub>1 \<and> P t\<^sub>2"
  by auto

lemma infinite_terms [clause_intro]: "infinite (UNIV :: ('f, 'v) term set)"
proof-
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI.

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest by blast
qed

lemma literal_cases: "\<lbrakk>\<P> \<in> {Pos, Neg}; \<P> = Pos \<Longrightarrow> P; \<P> = Neg \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

(* TODO: cases *)
method clause_simp uses (* cases*) simp intro =
  (*(-, (rule literal_cases[OF cases]))?,*)
  auto simp only: simp clause_simp clause_simp_term intro: intro clause_intro

method clause_auto uses simp intro = 
  (clause_simp simp: simp intro: intro)?,  
  (auto simp: simp intro intro)?, 
  (auto simp: simp clause_simp intro: intro clause_intro)?

type_synonym 'f ground_term = "'f gterm"

type_synonym 'f ground_context = "'f gctxt"
type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

type_synonym 'f ground_atom = "'f gatom"
type_synonym ('f, 'v) atom = "('f, 'v) term uprod"

(* For unified naming *)
locale vars_def = 
  fixes vars_def :: "'expression \<Rightarrow> 'variables" 
begin 

abbreviation "vars \<equiv> vars_def"

end

locale grounding_def = 
  fixes 
    to_ground_def :: "'non_ground \<Rightarrow> 'ground" and
    from_ground_def :: "'ground \<Rightarrow> 'non_ground"
begin 

abbreviation "to_ground \<equiv> to_ground_def"

abbreviation "from_ground \<equiv> from_ground_def"

end

(* Term *)

global_interpretation "term": vars_def where vars_def = vars_term.

global_interpretation "context": vars_def where vars_def = vars_ctxt.

global_interpretation "term": grounding_def where 
  to_ground_def = gterm_of_term and from_ground_def = term_of_gterm .

global_interpretation "context": grounding_def where 
  to_ground_def = gctxt_of_ctxt and from_ground_def = ctxt_of_gctxt.

global_interpretation
  "term": base_variable_substitution where 
    subst = subst_apply_term and id_subst = Var and comp_subst = "(\<odot>)" and 
    vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" +
  "term": finite_variables where vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" +
  "term": all_subst_ident_iff_ground where 
    is_ground = "term.is_ground :: ('f, 'v) term \<Rightarrow> bool" and subst = "(\<cdot>t)" +
  "term": grounding where 
    vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
    subst = "(\<cdot>t)" and to_ground = term.to_ground and from_ground = term.from_ground
proof unfold_locales
  show "\<And>t \<sigma> \<tau>. (\<And>x. x \<in> term.vars t \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> t \<cdot>t \<sigma> = t \<cdot>t \<tau>"
    using term_subst_eq.
next
  show "\<And>t. finite (term.vars t)"
    by simp
next
  show "\<And>t. (term.vars t = {}) = (\<forall>\<sigma>. t \<cdot>t \<sigma> = t)"
    using is_ground_trm_iff_ident_forall_subst.
next
  fix t :: "('f, 'v) term" and ts :: "('f, 'v) term set"

  assume "finite ts" "term.vars t \<noteq> {}"
  then show "\<exists>\<sigma>. t \<cdot>t \<sigma> \<noteq> t \<and> t \<cdot>t \<sigma> \<notin> ts"
  proof(induction t arbitrary: ts)
    case (Var x)

    obtain t' where t': "t' \<notin> ts" "is_Fun t'"
      using Var.prems(1) finite_list by blast

    define \<sigma> :: "('f, 'v) subst" where "\<And>x. \<sigma> x = t'"

    have "Var x \<cdot>t \<sigma> \<noteq> Var x"
      using t'
      unfolding \<sigma>_def
      by auto

    moreover have "Var x \<cdot>t \<sigma> \<notin> ts"
      using t'
      unfolding \<sigma>_def
      by simp

    ultimately show ?case
      using Var
      by blast
  next
    case (Fun f args)

    obtain a where a: "a \<in> set args" and a_vars: "term.vars a \<noteq> {}"
      using Fun.prems by fastforce

    then obtain \<sigma> where 
      \<sigma>: "a \<cdot>t \<sigma> \<noteq> a" and
      a_\<sigma>_not_in_args: "a \<cdot>t \<sigma> \<notin> \<Union> (set `  term.args ` ts)"
      by (metis Fun.IH Fun.prems(1) List.finite_set finite_UN finite_imageI)

    then have "Fun f args \<cdot>t \<sigma> \<noteq> Fun f args"
      by (metis a subsetI term.set_intros(4) term_subst.comp_subst.left.action_neutral 
          vars_term_subset_subst_eq)

    moreover have "Fun f args \<cdot>t \<sigma> \<notin> ts"
      using a a_\<sigma>_not_in_args
      by auto

    ultimately show ?case
      using Fun
      by blast
  qed
next
  show "\<And>\<gamma> t. (term.vars (t \<cdot>t \<gamma>) = {}) = (\<forall>x \<in> term.vars t. term.vars (\<gamma> x) = {})"
    by (meson is_ground_iff)
next
  show "\<exists>t. term.vars t = {}"
    by (meson vars_term_of_gterm)
next
  (* TODO: *)
  have "\<And>x. term.vars x = {} \<Longrightarrow> \<exists>g. term.from_ground g = x"
    by (metis (full_types) Term_Context.ground_vars_term_empty ground_substD ground_substI 
          ground_term_of_gterm gterm_of_term_inv term_subst.all_subst_ident_if_ground)

  then show "{f. term.vars f = {}} = range term.from_ground"
    by fastforce
next
  show "\<And>g. term.to_ground (term.from_ground g) = g"
    by simp
qed

(* Context *)

global_interpretation "context": all_subst_ident_iff_ground where 
  is_ground = "\<lambda>\<kappa>. context.vars \<kappa> = {}" and subst = "(\<cdot>t\<^sub>c)"
proof unfold_locales
  fix \<kappa> :: "('f, 'v) context"
  show "context.vars \<kappa> = {} = (\<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>)"
  proof (intro iffI)
    show "context.vars \<kappa> = {} \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
      by(induction \<kappa>) (simp_all add: list.map_ident_strong)
  next
    assume "\<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
  
    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> \<forall>\<sigma>. \<kappa>\<langle>t\<^sub>G\<rangle> \<cdot>t \<sigma> = \<kappa>\<langle>t\<^sub>G\<rangle>"
      by simp
  
    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> term.is_ground \<kappa>\<langle>t\<^sub>G\<rangle>"
      by (meson is_ground_trm_iff_ident_forall_subst)
  
    then show "context.vars \<kappa> = {}"
      by (metis sup.commute sup_bot_left vars_term_ctxt_apply vars_term_of_gterm)
  qed
next
  fix \<kappa> :: "('f, 'v) context" and \<kappa>s :: "('f, 'v) context set"
  assume finite: "finite \<kappa>s" and non_ground: "context.vars \<kappa> \<noteq> {}"

  then show "\<exists>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> \<noteq> \<kappa> \<and> \<kappa> \<cdot>t\<^sub>c \<sigma> \<notin> \<kappa>s"
  proof(induction \<kappa> arbitrary: \<kappa>s)
    case Hole
    then show ?case
      by simp
  next
    case (More f ts \<kappa> ts')

    show ?case
    proof(cases "context.vars \<kappa> = {}")
      case True

      let ?sub_terms = 
        "\<lambda>\<kappa> :: ('f, 'v) context. case \<kappa> of More _ ts _ ts' \<Rightarrow> set ts \<union> set ts'  | _ \<Rightarrow> {}"

      let ?\<kappa>s' = "set ts \<union> set ts' \<union> \<Union>(?sub_terms ` \<kappa>s)"

      from True obtain t where t: "t \<in> set ts \<union> set ts'" and non_ground: "\<not>term.is_ground t"
        using More.prems by auto

      have "\<And>\<kappa>. finite (?sub_terms \<kappa>)"
      proof-  
        fix \<kappa>
        show "finite (?sub_terms \<kappa>)"
          by(cases \<kappa>) simp_all
      qed

      then have "finite (\<Union>(?sub_terms ` \<kappa>s))"
        using More.prems(1) by blast

      then have finite: "finite ?\<kappa>s'"
        by blast

      obtain \<sigma> where \<sigma>: "t \<cdot>t \<sigma> \<noteq> t" and \<kappa>s': "t \<cdot>t \<sigma> \<notin> ?\<kappa>s'"
        using term.exists_non_ident_subst[OF finite non_ground]
        by blast

      have "More f ts \<kappa> ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts \<kappa> ts'"
        using t \<sigma>
        by (smt (verit, ccfv_threshold) Un_iff \<kappa>s' ctxt.inject ctxt.simps(3) image_iff 
            list.set_map subst_apply_ctxt.elims)

      moreover have " More f ts \<kappa> ts' \<cdot>t\<^sub>c \<sigma> \<notin> \<kappa>s"
        using \<kappa>s' t
        by auto

      ultimately show ?thesis
        by blast
    next
      case False

      let ?sub_contexts = "(\<lambda>\<kappa>. case \<kappa> of More _ _ \<kappa> _ \<Rightarrow> \<kappa>) ` {\<kappa> \<in> \<kappa>s. \<kappa> \<noteq> \<box>}"

      have "finite ?sub_contexts"
        using More.prems(1)
        by auto

      then obtain \<sigma> where \<sigma>: "\<kappa> \<cdot>t\<^sub>c \<sigma> \<noteq> \<kappa>" and sub_contexts: "\<kappa> \<cdot>t\<^sub>c \<sigma> \<notin> ?sub_contexts"
        using More.IH[OF _ False]
        by blast

      then have "More f ts \<kappa> ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts \<kappa> ts'"
        by simp

      moreover have "More f ts \<kappa> ts' \<cdot>t\<^sub>c \<sigma> \<notin> \<kappa>s"
        using sub_contexts
        by (metis (mono_tags, lifting) ctxt.distinct(1) ctxt.simps(5) image_eqI mem_Collect_eq 
            subst_apply_ctxt.simps(2))

      ultimately show ?thesis 
        by blast
    qed
  qed
qed

global_interpretation "context": based_variable_substitution where
  subst = "(\<cdot>t\<^sub>c)" and vars = context.vars and id_subst = Var and comp_subst = "(\<odot>)" and 
  base_vars = term.vars and base_subst = "(\<cdot>t)"
proof unfold_locales
  fix \<kappa> :: "('f, 'v) context"
  show "\<kappa> \<cdot>t\<^sub>c Var = \<kappa>"
    by (induction \<kappa>) auto
next
  show "\<And>\<kappa> \<sigma> \<tau>. \<kappa> \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = \<kappa> \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  show "\<And>\<kappa>. context.vars \<kappa> = {} \<Longrightarrow> \<forall>\<sigma>. \<kappa> \<cdot>t\<^sub>c \<sigma> = \<kappa>"
    using context.all_subst_ident_iff_ground by blast
next 
  show "\<And>a \<sigma> \<tau>. (\<And>x. x \<in> context.vars a \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> a \<cdot>t\<^sub>c \<sigma> = a \<cdot>t\<^sub>c \<tau>"
    using ctxt_subst_eq.
next
  fix \<gamma> :: "('f,'v) subst"

  show "(\<forall>\<kappa>. context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}) = (\<forall>t. term.is_ground (t \<cdot>t \<gamma>))"
  proof(intro iffI allI equals0I)
    fix t x

    assume is_ground: "\<forall>\<kappa>. context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}" and vars: "x \<in> term.vars (t \<cdot>t \<gamma>)"

    have "\<And>f. context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>) = {}"
      using is_ground
      by presburger

    moreover have "\<And>f. x \<in> context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>)"
      using vars
      by simp
      
    ultimately show False
      by blast
  next
    fix \<kappa> x
    assume is_ground: "\<forall>t. term.is_ground (t \<cdot>t \<gamma>)" and vars: "x \<in> context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>)"

    have "\<And>t. term.is_ground (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using is_ground
      by presburger

    moreover have "\<And>t. x \<in> term.vars (\<kappa>\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  qed
next
  fix \<kappa> and \<gamma> :: "('f, 'v) subst"

  show "(context.vars (\<kappa> \<cdot>t\<^sub>c \<gamma>) = {}) = (\<forall>x \<in> context.vars \<kappa>. term.is_ground (\<gamma> x))"
    by(induction \<kappa>)(auto simp: term.is_grounding_iff_vars_grounded)
qed

global_interpretation "context": finite_variables where vars = context.vars
proof unfold_locales 
  fix \<kappa> :: "('f, 'v) context"

  have "\<And>t. finite (term.vars \<kappa>\<langle>t\<rangle>)"
    using term.finite_vars by blast

  then show "finite (context.vars \<kappa>)"
    unfolding vars_term_ctxt_apply finite_Un
    by simp
qed

global_interpretation "context": grounding where 
  vars = "context.vars :: ('f, 'v) context \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
  subst = "(\<cdot>t\<^sub>c)" and from_ground = context.from_ground and to_ground = context.to_ground
proof unfold_locales
  have "\<And>x. context.vars x = {} \<Longrightarrow> \<exists>g. context.from_ground g = x"
    by (metis Un_empty_left gctxt_of_ctxt_inv term.ground_exists term.to_ground_inverse 
        term_of_gterm_ctxt_apply_ground(1) vars_term_ctxt_apply)

  then show "{f. context.vars f = {}} = range context.from_ground"
    by force
next 
  show "\<And>g. context.to_ground (context.from_ground g) = g"
    by simp
qed

(* Lifiting *)

(* TODO: names *)
lemma exists_uprod: "\<exists>a. t \<in> set_uprod a"
  by (metis insertI1 set_uprod_simps)

lemma exists_literal: "\<exists>l. a \<in> set_literal l"
  by (meson literal.set_intros(1))

lemma exists_mset: "\<exists>c. l \<in> set_mset c"
  by (meson union_single_eq_member)

lemma finite_set_literal: "\<And>l. finite (set_literal l)"
  unfolding set_literal_atm_of
  by simp

locale clause_lifting =
  based_variable_substitution_lifting where 
    base_subst = "(\<cdot>t)" and base_vars = term.vars and id_subst = Var and comp_subst = "(\<odot>)" + 
  all_subst_ident_iff_ground_lifting where id_subst = Var and comp_subst = "(\<odot>)" +
  grounding_lifting where id_subst = Var and comp_subst = "(\<odot>)" 

global_interpretation atom: clause_lifting where 
  sub_subst = "(\<cdot>t)" and  sub_vars = term.vars and map = map_uprod and to_set = set_uprod and 
  sub_to_ground = term.to_ground and sub_from_ground = term.from_ground and 
  to_ground_map = map_uprod and from_ground_map = map_uprod and ground_map = map_uprod and 
  to_set_ground = set_uprod
  by 
    unfold_locales 
    (auto 
      simp: uprod.map_comp uprod.map_id uprod.set_map exists_uprod 
      term.is_grounding_iff_vars_grounded 
      intro: uprod.map_cong)

global_interpretation literal: clause_lifting where 
  sub_subst = atom.subst and sub_vars = atom.vars and map = map_literal and 
  to_set = set_literal and sub_to_ground = atom.to_ground and 
  sub_from_ground = atom.from_ground and to_ground_map = map_literal and 
  from_ground_map = map_literal and ground_map = map_literal and to_set_ground = set_literal
  by
    unfold_locales 
    (auto 
      simp: literal.map_comp literal.map_id literal.set_map exists_literal atom.is_ground_iff
        finite_set_literal
      intro: literal.map_cong)

global_interpretation clause: clause_lifting
  where sub_subst = literal.subst and sub_vars = literal.vars and map = image_mset and
    to_set = set_mset and sub_to_ground = literal.to_ground and sub_from_ground = literal.from_ground and 
    to_ground_map = image_mset and from_ground_map = image_mset and ground_map = image_mset and to_set_ground = set_mset
  by unfold_locales 
    (auto simp: exists_mset literal.is_ground_iff)

notation atom.subst (infixl "\<cdot>a" 67)
notation literal.subst (infixl "\<cdot>l" 66)
notation clause.subst (infixl "\<cdot>" 67)

lemmas [clause_simp] = literal.to_set_is_ground atom.to_set_is_ground

lemma xx [clause_simp]: "term \<in># mset_lit literal \<longleftrightarrow> term \<in> \<Union>(set_uprod ` set_literal literal)"
  by (metis UN_insert Union_image_empty literal.set_cases literal.set_sel(1) literal.set_sel(2) mset_lit.simps(1) mset_lit.simps(2) set_literal_atm_of set_mset_mset_uprod union_iff)

(* TODO: Directly from "is_ground {#}" *)
lemma clause_subst_empty [clause_simp]: "{#} \<cdot> \<sigma> = {#}" "clause \<cdot> \<sigma> = {#} \<longleftrightarrow> clause = {#}"
  by (simp_all add: clause.subst_def)

lemma vars_atom [clause_simp]: 
  "atom.vars (Upair term\<^sub>1 term\<^sub>2) = term.vars term\<^sub>1 \<union> term.vars term\<^sub>2"
  by (simp_all add: atom.vars_def)

lemma vars_literal [clause_simp]: 
  "literal.vars (Pos atom) = atom.vars atom"
  "literal.vars (Neg atom) = atom.vars atom"
  "literal.vars ((if b then Pos else Neg) atom) = atom.vars atom"
  by (simp_all add: literal.vars_def)

(* TODO: Can these be generalized? *)
lemma vars_clause_add_mset [clause_simp]: 
  "clause.vars (add_mset literal clause) = literal.vars literal \<union> clause.vars clause"
  by (simp add: clause.vars_def)

lemma vars_clause_plus [clause_simp]: 
  "clause.vars (clause\<^sub>1 + clause\<^sub>2) = clause.vars clause\<^sub>1 \<union> clause.vars clause\<^sub>2"
  by (simp add: clause.vars_def)

lemma clause_submset_vars_clause_subset [clause_intro]: 
  "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> clause.vars clause\<^sub>1 \<subseteq> clause.vars clause\<^sub>2"
  by (metis subset_mset.add_diff_inverse sup_ge1 vars_clause_plus)

lemma empty_clause_is_ground [clause_simp]: "clause.is_ground {#}"
  unfolding clause.vars_def
  by simp

lemma term_context_ground_iff_term_is_ground [clause_simp]:
  "Term_Context.ground term = term.is_ground term"
  by(induction "term") auto

lemma ground_ctxt_iff_context_is_ground [clause_simp]: 
  "ground_ctxt context = context.is_ground context"
  by(induction "context") clause_auto
 
lemma subst_atom [clause_simp]: 
  "Upair term\<^sub>1 term\<^sub>2 \<cdot>a \<sigma> = Upair (term\<^sub>1 \<cdot>t \<sigma>) (term\<^sub>2 \<cdot>t \<sigma>)"
  unfolding atom.subst_def
  by simp_all
  
lemma subst_literal [clause_simp]: 
  "Pos atom \<cdot>l \<sigma> = Pos (atom \<cdot>a \<sigma>)"
  "Neg atom \<cdot>l \<sigma> = Neg (atom \<cdot>a \<sigma>)"
  "atm_of (literal \<cdot>l \<sigma>) = atm_of literal \<cdot>a \<sigma>"
  unfolding literal.subst_def
  using literal.map_sel
  by auto

(* TODO: Can these be generalized? *)
lemma subst_clause_add_mset [clause_simp]: 
  "add_mset literal clause \<cdot> \<sigma> = add_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding clause.subst_def
  by simp

lemma subst_clause_remove1_mset [clause_simp]: 
  assumes "literal \<in># clause" 
  shows "remove1_mset literal clause \<cdot> \<sigma> = remove1_mset (literal \<cdot>l \<sigma>) (clause \<cdot> \<sigma>)"
  unfolding clause.subst_def image_mset_remove1_mset_if
  using assms
  by simp

lemma subst_clause_plus [clause_simp]: 
  "(clause\<^sub>1 + clause\<^sub>2) \<cdot> \<sigma> = clause\<^sub>1 \<cdot> \<sigma> + clause\<^sub>2 \<cdot> \<sigma>"
  unfolding clause.subst_def
  by simp

lemma sub_ground_clause [clause_intro]: 
  assumes "clause' \<subseteq># clause" "clause.is_ground clause"
  shows "clause.is_ground clause'"
  using assms
  unfolding clause.vars_def
  by blast

lemma mset_mset_lit_subst [clause_simp]: 
  "{# term \<cdot>t \<sigma>. term \<in># mset_lit literal #} = mset_lit (literal \<cdot>l \<sigma>)"
  unfolding literal.subst_def atom.subst_def
  by (cases literal) (auto simp: mset_uprod_image_mset)

(* TODO: Use subst_in_to_set_subst *)
lemma term_in_literal_subst [clause_intro]: 
  assumes "term \<in># mset_lit literal" 
  shows "term \<cdot>t \<sigma> \<in># mset_lit (literal \<cdot>l \<sigma>)"
  using assms 
  apply clause_simp
  apply (simp add: atom.subst_in_to_set_subst)
  using atom.subst_in_to_set_subst literal.subst_in_to_set_subst by blast

lemmas literal_in_clause_subst [clause_intro] = clause.subst_in_to_set_subst

lemma subst_polarity_stable: 
  shows 
    subst_neg_stable: "is_neg (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_neg literal" and
    subst_pos_stable: "is_pos (literal \<cdot>l \<sigma>) \<longleftrightarrow> is_pos literal"
  by (simp_all add: literal.subst_def)

(* TODO: Could these be made less explicit somehow?
Something like:
locale conversion =
  fixes to :: "'a \<Rightarrow> 'b" and "from" :: "'b \<Rightarrow> 'a"
  assumes 
    inv: "\<And>x. from (to x) = x" and
    inj_to: "\<And>X. inj_on to X" and
    inj_from: "\<And>domain. inj_on from (to ` domain)"
?
 *)


lemma atom_from_ground_term_from_ground [clause_simp]:
  "atom.from_ground (Upair term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2) = Upair (term.from_ground term\<^sub>G\<^sub>1) (term.from_ground term\<^sub>G\<^sub>2)"
  by (simp add: atom.from_ground_def)

lemma literal_from_ground_atom_from_ground [clause_simp]: 
  "literal.from_ground (Neg atom\<^sub>G) = Neg (atom.from_ground atom\<^sub>G)"
  "literal.from_ground (Pos atom\<^sub>G) = Pos (atom.from_ground atom\<^sub>G)"  
  by (simp_all add: literal.from_ground_def)

lemma context_from_ground_hole [clause_simp]: "context.from_ground context\<^sub>G = \<box> \<longleftrightarrow> context\<^sub>G = \<box>\<^sub>G"
  by(cases context\<^sub>G) simp_all

lemma clause_from_ground_empty_mset [clause_simp]: "clause.from_ground {#} = {#}"
  by (simp add: clause.from_ground_def)

lemma clause_to_ground_empty_mset [clause_simp]: "clause.to_ground {#} = {#}"
  by (simp add: clause.to_ground_def)

lemmas ground_term_is_ground [clause_intro] = vars_term_of_gterm

lemmas ground_context_is_ground [clause_intro] = vars_ctxt_of_gctxt

lemma term_with_context_is_ground [clause_simp]: 
  "term.is_ground context\<langle>term\<rangle> \<longleftrightarrow> context.is_ground context \<and> term.is_ground term"
  by simp

lemma ground_atom_is_ground [simp]: "atom.is_ground (atom.from_ground atom\<^sub>G)"
  using atom.ground_is_ground.

lemma ground_literal_is_ground [simp]: "literal.is_ground (literal.from_ground literal\<^sub>G)"
  using literal.ground_is_ground.

lemma ground_clause_is_ground [simp]: "clause.is_ground (clause.from_ground clause\<^sub>G)"
  using clause.ground_is_ground.

lemma literal_from_ground_polarity_stable: 
  shows 
    literal_from_ground_neg_stable: "is_neg literal\<^sub>G \<longleftrightarrow> is_neg (literal.from_ground literal\<^sub>G)" and
    literal_from_ground_stable: "is_pos literal\<^sub>G \<longleftrightarrow> is_pos (literal.from_ground literal\<^sub>G)"
  by (simp_all add: literal.from_ground_def)

lemmas term_from_ground_inverse = term_of_gterm_inv

lemmas context_from_ground_inverse = ctxt_of_gctxt_inv

lemma atom_from_ground_inverse [simp]: 
  "atom.to_ground (atom.from_ground atom) = atom"
  using atom.from_ground_inverse.

lemma literal_from_ground_inverse [simp]: 
  "literal.to_ground (literal.from_ground literal) = literal"
  using literal.from_ground_inverse.

lemma clause_from_ground_inverse [simp]: 
  "clause.to_ground (clause.from_ground clause) = clause"
  using clause.from_ground_inverse.

lemma ground_term_with_context1:
  assumes "context.is_ground context" "term.is_ground term"
  shows "(context.to_ground context)\<langle>term.to_ground term\<rangle>\<^sub>G = term.to_ground context\<langle>term\<rangle>"
  using assms
  by (simp add: term_context_ground_iff_term_is_ground)

lemma ground_term_with_context2:
  assumes "context.is_ground context"  
  shows "term.from_ground (context.to_ground context)\<langle>term\<^sub>G\<rangle>\<^sub>G = context\<langle>term.from_ground term\<^sub>G\<rangle>"
  using assms
  by (simp add: ground_ctxt_iff_context_is_ground ground_gctxt_of_ctxt_apply_gterm)

lemma ground_term_with_context3: 
  "(context.from_ground context\<^sub>G)\<langle>term.from_ground term\<^sub>G\<rangle> = term.from_ground context\<^sub>G\<langle>term\<^sub>G\<rangle>\<^sub>G"
  using ground_term_with_context2[OF ground_context_is_ground, symmetric]
  unfolding context.from_ground_inverse.

lemmas ground_term_with_context =
  ground_term_with_context1
  ground_term_with_context2
  ground_term_with_context3

lemma context_is_ground_context_compose1:
  assumes "context.is_ground (context \<circ>\<^sub>c context')"
  shows "context.is_ground context" "context.is_ground context'"
  using assms
  by(induction "context" context' rule: ctxt_compose.induct) auto

lemma context_is_ground_context_compose2:
  assumes "context.is_ground context" "context.is_ground context'" 
  shows "context.is_ground (context \<circ>\<^sub>c context')"
  using assms
  by (meson ground_ctxt_comp ground_ctxt_iff_context_is_ground)

lemmas context_is_ground_context_compose = 
  context_is_ground_context_compose1 
  context_is_ground_context_compose2

lemma ground_context_subst:
  assumes 
    "context.is_ground context\<^sub>G" 
    "context\<^sub>G = (context \<cdot>t\<^sub>c \<sigma>) \<circ>\<^sub>c context'"
  shows 
    "context\<^sub>G = context \<circ>\<^sub>c context' \<cdot>t\<^sub>c \<sigma>"
  using assms 
proof(induction "context")
  case Hole
  then show ?case
    by simp
next
  case More
  then show ?case
    using context_is_ground_context_compose1(2)
    by (metis subst_compose_ctxt_compose_distrib context.subst_ident_if_ground)
qed
   
lemma ground_term_subst_upd [simp]:
  assumes "term.is_ground update" "term.is_ground (term \<cdot>t \<gamma>)" 
  shows "term.is_ground (term \<cdot>t \<gamma>(var := update))"
  using assms  
  by (simp add: is_ground_iff)

lemma ground_atom_subst_upd [simp]:
  assumes "term.is_ground update" "atom.is_ground (atom \<cdot>a \<gamma>)" 
  shows "atom.is_ground (atom \<cdot>a \<gamma>(var := update))"
  using assms
  unfolding atom.subst_def atom.vars_def
  by(cases atom) simp

lemma ground_literal_subst_upd [simp]:
  assumes "term.is_ground update" "literal.is_ground (literal \<cdot>l \<gamma>)" 
  shows "literal.is_ground (literal \<cdot>l \<gamma>(var := update))"
  using assms
  unfolding literal.subst_def literal.vars_def
  by(cases literal) simp_all

lemma ground_clause_subst_upd [simp]:
  assumes "term.is_ground update" "clause.is_ground (clause \<cdot> \<gamma>)" 
  shows "clause.is_ground (clause \<cdot> \<gamma>(var := update))"
  using clause.ground_subst_upd[OF assms].

lemma clause_from_ground_add_mset [clause_simp]: 
  "clause.from_ground (add_mset literal\<^sub>G clause\<^sub>G) = 
    add_mset (literal.from_ground literal\<^sub>G) (clause.from_ground clause\<^sub>G)"
  by (simp add: clause.from_ground_def)

lemma set_mset_clause_from_ground_literal_from_ground: 
  "set_mset (clause.from_ground clause) = literal.from_ground ` (set_mset clause)"
  by (simp add: clause.from_ground_def)

lemma remove1_mset_literal_from_ground: 
  "remove1_mset (literal.from_ground literal\<^sub>G) (clause.from_ground clause\<^sub>G) 
   = clause.from_ground (remove1_mset literal\<^sub>G clause\<^sub>G)"
  unfolding clause.from_ground_def image_mset_remove1_mset[OF literal.inj_from_ground]..

lemma ground_term_in_ground_atom [clause_simp]:
  assumes "term \<in> set_uprod atom" "atom.is_ground atom"
  shows "term.is_ground term"
  using assms
  by (simp add: atom.vars_def)

lemma ground_terms_in_ground_atom1:
  assumes "term.is_ground term\<^sub>1" and "term.is_ground term\<^sub>2"
  shows "Upair (term.to_ground term\<^sub>1) (term.to_ground term\<^sub>2) = atom.to_ground (Upair term\<^sub>1 term\<^sub>2)"
  using assms
  by (simp add: atom.to_ground_def)

lemma ground_terms_in_ground_atom2 [clause_simp]: 
  "atom.is_ground (Upair term\<^sub>1 term\<^sub>2) \<longleftrightarrow> term.is_ground term\<^sub>1 \<and> term.is_ground term\<^sub>2"
  by clause_simp

lemmas ground_terms_in_ground_atom = 
  ground_terms_in_ground_atom1
  ground_terms_in_ground_atom2

lemma ground_atom_in_ground_literal1 [intro]:
  assumes "atom \<in> set_literal literal" "literal.is_ground literal" 
  shows "atom.is_ground atom"
  using assms
  by (simp add: literal.vars_def)

lemma ground_atom_in_ground_literal2:
    "Pos (atom.to_ground atom) = literal.to_ground (Pos atom)" 
    "Neg (atom.to_ground atom) = literal.to_ground (Neg atom)" 
  by (simp_all add: literal.to_ground_def)

lemmas ground_atom_in_ground_literal = 
  ground_atom_in_ground_literal1
  ground_atom_in_ground_literal2

lemma atom_is_ground_in_ground_literal [intro]:
  "literal.is_ground literal \<longleftrightarrow> atom.is_ground (atm_of literal)"
  by (simp add: literal.vars_def set_literal_atm_of)

lemma ground_term_in_ground_literal:
  assumes "literal.is_ground literal"  "term \<in># mset_lit literal"  
  shows "term.is_ground term"
  using assms
  by clause_simp

lemma ground_term_in_ground_literal_subst:
  assumes "literal.is_ground (literal \<cdot>l \<gamma>)" "term \<in># mset_lit literal"  
  shows "term.is_ground (term \<cdot>t \<gamma>)"
  using ground_term_in_ground_literal[OF assms(1) term_in_literal_subst[OF assms(2)]].

lemma ground_literal_in_ground_clause1:
  assumes "literal \<in># clause" "clause.is_ground clause" 
  shows "literal.is_ground literal"
  using assms
  by (simp add: clause.vars_def)

lemma ground_literal_in_ground_clause2: 
  "literal \<in># clause.from_ground clause\<^sub>G \<Longrightarrow> literal.is_ground literal"
  by (simp add: ground_literal_in_ground_clause1)

lemma ground_literal_in_ground_clause3: 
  "literal\<^sub>G \<in># clause\<^sub>G \<longleftrightarrow> literal.from_ground literal\<^sub>G \<in># clause.from_ground clause\<^sub>G"
  using clause.from_ground_inverse literal.from_ground_inverse
  by (simp add: inj_image_mem_iff set_mset_clause_from_ground_literal_from_ground literal.inj_from_ground)

lemma ground_literal_in_ground_clause4: 
  "(\<forall>literal \<in># clause.from_ground clause\<^sub>G. P literal) \<longleftrightarrow> (\<forall>literal\<^sub>G \<in># clause\<^sub>G. P (literal.from_ground literal\<^sub>G))"
  using set_mset_clause_from_ground_literal_from_ground image_iff
  by (metis (no_types, opaque_lifting))

lemmas ground_literal_in_ground_clause = 
  ground_literal_in_ground_clause1
  ground_literal_in_ground_clause2
  ground_literal_in_ground_clause3
  ground_literal_in_ground_clause4

lemma ground_literal_in_ground_clause_subst:
  assumes "clause.is_ground (clause \<cdot> \<gamma>)"  "literal \<in># clause"  
  shows "literal.is_ground (literal \<cdot>l \<gamma>)"
  using clause.to_set_is_ground_subst[OF assms(2,1)]. 

lemma term_to_ground_inverse [simp]:
  assumes "term.is_ground term"  
  shows "term.from_ground (term.to_ground term) = term"
  using assms
  by (cases "term") (simp_all add: map_idI term_context_ground_iff_term_is_ground)

lemma atom_to_ground_inverse [simp]: 
  assumes "atom.is_ground atom"  
  shows "atom.from_ground (atom.to_ground atom) = atom"
  using atom.to_ground_inverse[OF assms].
 
lemma literal_to_ground_inverse [simp]: 
  assumes "literal.is_ground literal"  
  shows "literal.from_ground (literal.to_ground literal) = literal"
  using literal.to_ground_inverse[OF assms].
 
lemma clause_to_ground_inverse [simp]: 
  assumes "clause.is_ground clause"  
  shows "clause.from_ground (clause.to_ground clause) = clause"
  using clause.to_ground_inverse[OF assms].

lemma clause_to_ground_plus [simp]: 
  "clause.to_ground (clause\<^sub>1 + clause\<^sub>2) = clause.to_ground clause\<^sub>1 + clause.to_ground clause\<^sub>2"
  by (simp add: clause.to_ground_def)

lemma clause_from_ground_plus [simp]: 
  "clause.from_ground (clause\<^sub>G\<^sub>1 + clause\<^sub>G\<^sub>2) = clause.from_ground clause\<^sub>G\<^sub>1 + clause.from_ground clause\<^sub>G\<^sub>2"
  by (simp add: clause.from_ground_def)

lemma mset_literal_from_ground: "mset_lit (literal.from_ground l) = image_mset term.from_ground (mset_lit l)"
  by (metis atom.from_ground_def literal.from_ground_def literal.map_cong0 mset_lit_image_mset)

lemma clause_is_ground_add_mset [clause_simp]: "clause.is_ground (add_mset literal clause) \<longleftrightarrow> 
  literal.is_ground literal \<and> clause.is_ground clause"
  by clause_auto

lemma clause_to_ground_add_mset:
  assumes "clause.from_ground clause = add_mset literal clause'" 
  shows "clause = add_mset (literal.to_ground literal) (clause.to_ground clause')"
  using assms
  by (metis clause.from_ground_inverse clause.to_ground_def image_mset_add_mset)

lemma obtain_from_atom_subst [clause_intro]: 
  assumes "Upair term\<^sub>1' term\<^sub>2' = atom \<cdot>a \<sigma>"
  obtains term\<^sub>1 term\<^sub>2 
  where "atom = Upair term\<^sub>1 term\<^sub>2" "term\<^sub>1' = term\<^sub>1 \<cdot>t \<sigma>" "term\<^sub>2' = term\<^sub>2 \<cdot>t \<sigma>"
  using assms
  unfolding atom.subst_def
  by(cases atom) auto

lemma obtain_from_pos_literal_subst [clause_intro]: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' \<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 \<approx> term\<^sub>2" "term\<^sub>1' = term\<^sub>1 \<cdot>t \<sigma>" "term\<^sub>2' = term\<^sub>2 \<cdot>t \<sigma>"
  using assms obtain_from_atom_subst subst_pos_stable
  by (metis is_pos_def literal.sel(1) subst_literal(1))

lemma obtain_from_neg_literal_subst: 
  assumes "literal \<cdot>l \<sigma> = term\<^sub>1' !\<approx> term\<^sub>2'"
  obtains term\<^sub>1 term\<^sub>2 
  where "literal = term\<^sub>1 !\<approx> term\<^sub>2" "term\<^sub>1 \<cdot>t \<sigma> = term\<^sub>1'" "term\<^sub>2 \<cdot>t \<sigma> = term\<^sub>2'"
  using assms obtain_from_atom_subst subst_neg_stable
  by (metis literal.collapse(2) literal.disc(2) literal.sel(2) subst_literal(3))

lemmas obtain_from_literal_subst = obtain_from_pos_literal_subst obtain_from_neg_literal_subst

lemma var_is_not_ground: "is_Var t \<Longrightarrow> \<not>term.is_ground t"
  by (metis empty_iff term.set_sel(3))

lemma subst_cannot_add_var:
  assumes "is_Var (term \<cdot>t \<sigma>)"  
  shows "is_Var term"
  using assms term.subst_cannot_unground[OF var_is_not_ground] 
  by fastforce

lemma var_in_term:
  assumes "var \<in> term.vars term"
  obtains "context" where "term = context\<langle>Var var\<rangle>"
  using assms
proof(induction "term")
  case Var
  then show ?case
    by (metis Term.term.simps(17) ctxt_apply_term.simps(1) singletonD)
next
  case (Fun f args)
  then obtain term' where "term' \<in> set args " "var \<in> term.vars term'"
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

lemma var_in_non_ground_term: 
  assumes "\<not> term.is_ground term"
  obtains "context" var where "term = context\<langle>var\<rangle>" "is_Var var"
proof-
  obtain var where "var \<in> term.vars term"
    using assms
    by blast

  moreover then obtain "context" where "term = context\<langle>Var var\<rangle>"
    using var_in_term
    by metis

  ultimately show ?thesis
    using that
    by blast
qed

lemma obtain_ground_subst:
  obtains \<gamma> 
  where "term_subst.is_ground_subst \<gamma>"
proof-
  obtain t\<^sub>G :: "('b, 'a) Term.term" where "term.is_ground t\<^sub>G"
    by (meson ground_term_is_ground)

  then have "term_subst.is_ground_subst  (\<lambda>_. t\<^sub>G)"
    by (simp add: is_ground_iff term_subst.is_ground_subst_def)

  with that show ?thesis
    by blast
qed

lemma ground_subst_exstension_term:
  assumes "term.is_ground (term \<cdot>t \<gamma>)"
  obtains \<gamma>'  :: "('f, 'v) subst"
  where "term \<cdot>t \<gamma> = term \<cdot>t \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  using assms
proof-
  obtain \<gamma>'' :: "'v \<Rightarrow> ('f, 'v) Term.term" where 
    \<gamma>'': "term_subst.is_ground_subst \<gamma>''"
    using obtain_ground_subst
    by blast

  define \<gamma>' where 
    \<gamma>':  "\<gamma>' = (\<lambda>var. if var \<in> term.vars term then \<gamma> var else \<gamma>'' var)"

  have "term_subst.is_ground_subst \<gamma>'"
    using assms \<gamma>'' 
    unfolding \<gamma>' term_subst.is_ground_subst_def
    by (simp add: is_ground_iff)

  moreover have "term \<cdot>t \<gamma> = term \<cdot>t \<gamma>'"
    unfolding \<gamma>'
    by (smt (verit, best) term_subst_eq)

  ultimately show ?thesis
    using that
    by blast
qed

lemma ground_subst_exstension_atom:
  assumes "atom.is_ground (atom \<cdot>a \<gamma>)"
  obtains \<gamma>'
  where "atom \<cdot>a \<gamma> = atom \<cdot>a \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  using atom.ground_subst_extension[OF assms]
  by auto

lemma ground_subst_exstension_literal:
  assumes "literal.is_ground (literal \<cdot>l \<gamma>)"
  obtains \<gamma>'
  where "literal \<cdot>l \<gamma> = literal \<cdot>l \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  using literal.ground_subst_extension[OF assms]
  by auto

lemma ground_subst_exstension_clause:
  assumes "clause.is_ground (clause \<cdot> \<gamma>)"
  obtains \<gamma>'
  where "clause \<cdot> \<gamma> = clause \<cdot> \<gamma>'" and "term_subst.is_ground_subst \<gamma>'"
  using clause.ground_subst_extension[OF assms]
  by auto
 
lemma non_ground_arg: 
  assumes "\<not> term.is_ground (Fun f terms)"
  obtains "term"
  where "term \<in> set terms" "\<not> term.is_ground term"
  using assms that by fastforce

lemma non_ground_arg': 
  assumes "\<not> term.is_ground (Fun f terms)"
  obtains ts1 var ts2 
  where "terms = ts1 @ [var] @ ts2" "\<not> term.is_ground var"
  using non_ground_arg
  by (metis append.left_neutral append_Cons assms split_list)

subsection \<open>Interpretations\<close>

lemma vars_term_ms_count:
  assumes "term.is_ground term\<^sub>G"
  shows "size {#var' \<in># vars_term_ms context\<langle>Var var\<rangle>. var' = var#} = 
         Suc (size {#var' \<in># vars_term_ms context\<langle>term\<^sub>G\<rangle>. var' = var#})"
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

context
  fixes I :: "('f gterm \<times> 'f gterm) set"
  assumes 
    trans: "trans I" and
    sym: "sym I" and
    compatible_with_gctxt: "compatible_with_gctxt I"
begin

lemma interpretation_context_congruence:
  assumes 
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<in> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  using 
    assms sym trans compatible_with_gctxt
    compatible_with_gctxtD symE transE 
  by meson

lemma interpretation_context_congruence':
  assumes 
    "(t, t') \<in> I"
    "(ctxt\<langle>t\<rangle>\<^sub>G, t'') \<notin> I"
  shows
    "(ctxt\<langle>t'\<rangle>\<^sub>G, t'') \<notin> I"
  using assms sym trans compatible_with_gctxt
  by (metis interpretation_context_congruence symD)

context
  fixes 
    \<gamma> :: "('f, 'v) subst" and
    update :: "('f, 'v) Term.term" and
    var :: 'v
  assumes
    update_is_ground: "term.is_ground update" and
    var_grounding: "term.is_ground (Var var \<cdot>t \<gamma>)" 
begin

lemma interpretation_term_congruence:
  assumes 
    term_grounding: "term.is_ground (term \<cdot>t \<gamma>)" and
    var_update: "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I" and
    updated_term: "(term.to_ground (term \<cdot>t \<gamma>(var := update)), term') \<in> I" 
  shows 
    "(term.to_ground (term \<cdot>t \<gamma>), term') \<in> I"
  using assms
proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms term))" arbitrary: "term")
  case 0

  then have "var \<notin> term.vars term"
    by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms size_eq_0_iff_empty)

  then have "term \<cdot>t \<gamma>(var := update) = term \<cdot>t \<gamma>"
    using term.subst_reduntant_upd 
    by fast

  with 0 show ?case
    by argo
next
  case (Suc n)

  then have "var \<in> term.vars term"
    by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms 
        zero_less_Suc)

  then obtain "context" where 
    "term" [simp]: "term = context\<langle>Var var\<rangle>"
    by (meson var_in_term)

  have [simp]: "(context.to_ground (context \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G = 
    term.to_ground (context\<langle>Var var\<rangle> \<cdot>t \<gamma>)"
    using Suc by fastforce

  have context_update [simp]: 
    "(context.to_ground (context \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground update\<rangle>\<^sub>G = 
      term.to_ground (context\<langle>update\<rangle> \<cdot>t \<gamma>)"
    using Suc update_is_ground
    unfolding "term"
    by auto

  have "n = size {#var' \<in># vars_term_ms context\<langle>update\<rangle>. var' = var#}"
    using Suc vars_term_ms_count[OF update_is_ground, of var "context"]
    by auto

  moreover have "term.is_ground (context\<langle>update\<rangle> \<cdot>t \<gamma>)"
    using Suc.prems update_is_ground 
    by auto

  moreover have  "(term.to_ground (context\<langle>update\<rangle> \<cdot>t \<gamma>(var := update)), term') \<in> I"
    using Suc.prems update_is_ground
    by auto

  moreover have update: "(term.to_ground update, term.to_ground (\<gamma> var)) \<in> I"
    using var_update sym
    by (metis symD)

  moreover have "(term.to_ground (context\<langle>update\<rangle> \<cdot>t \<gamma>), term') \<in> I"
    using Suc calculation
    by blast

  ultimately have "((context.to_ground (context \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G, term') \<in> I"
    using interpretation_context_congruence context_update
    by presburger

  then show ?case 
    unfolding "term"
    by simp
qed

lemma interpretation_term_congruence':
  assumes 
    term_grounding: "term.is_ground (term \<cdot>t \<gamma>)" and
    var_update: "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I" and
    updated_term: "(term.to_ground (term \<cdot>t \<gamma>(var := update)), term') \<notin> I" 
  shows
    "(term.to_ground (term \<cdot>t \<gamma>), term') \<notin> I"
proof
  assume "(term.to_ground (term \<cdot>t \<gamma>), term') \<in> I"

  then show False
    using 
      First_Order_Clause.interpretation_term_congruence[OF 
        trans sym compatible_with_gctxt var_grounding
        ]
      assms 
      sym 
      update_is_ground 
    by (smt (verit) eval_term.simps fun_upd_same fun_upd_triv fun_upd_upd ground_term_subst_upd 
        symD)
qed

lemma interpretation_atom_congruence:
  assumes 
    "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" 
    "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
    "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>(var := update)), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<in> I" 
  shows
    "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>)) \<in> I"
  using assms
  by (metis interpretation_term_congruence sym symE)

lemma interpretation_atom_congruence':
  assumes 
    "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" 
    "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)" 
    "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
    "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>(var := update)), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<notin> I" 
  shows
    "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>)) \<notin> I"
  using assms
  by (metis interpretation_term_congruence' sym symE)

lemma interpretation_literal_congruence:
  assumes
    "literal.is_ground (literal \<cdot>l \<gamma>)"
    "upair ` I \<TTurnstile>l term.to_ground (Var var \<cdot>t \<gamma>) \<approx> term.to_ground update"
    "upair ` I \<TTurnstile>l literal.to_ground (literal \<cdot>l \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile>l literal.to_ground (literal \<cdot>l \<gamma>)"
proof(cases literal)
  case (Pos atom)

  have "atom.to_ground (atom \<cdot>a \<gamma>) \<in> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"
      using Pos assms
      by clause_auto

    have "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
      using sym assms by auto

    moreover have 
      "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>(var := update)), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<in> I"
      using assms Pos Upair
      unfolding literal.to_ground_def atom.to_ground_def
      by(auto simp: subst_atom sym subst_literal)

    ultimately show ?thesis
      using interpretation_atom_congruence[OF term_groundings]
      by (simp add: Upair sym subst_atom atom.to_ground_def)
  qed

  with Pos show ?thesis
    by (metis ground_atom_in_ground_literal(2) subst_literal(1) true_lit_simps(1))
next
  case (Neg atom)

  have "atom.to_ground (atom \<cdot>a \<gamma>) \<notin> upair ` I"
  proof(cases atom)
    case (Upair term\<^sub>1 term\<^sub>2)  
    then have term_groundings: "term.is_ground (term\<^sub>1 \<cdot>t \<gamma>)" "term.is_ground (term\<^sub>2 \<cdot>t \<gamma>)"
      using Neg assms
      by clause_auto

    have "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I"
      using sym assms by auto

    moreover have 
      "(term.to_ground (term\<^sub>1 \<cdot>t \<gamma>(var := update)), term.to_ground (term\<^sub>2 \<cdot>t \<gamma>(var := update))) \<notin> I"
      using assms Neg Upair
      unfolding literal.to_ground_def atom.to_ground_def
      by (simp add: sym subst_literal(2) subst_atom)

    ultimately show ?thesis
      using interpretation_atom_congruence'[OF term_groundings]
      by (simp add: Upair sym subst_atom atom.to_ground_def)
  qed

  then show ?thesis
    by (metis Neg ground_atom_in_ground_literal2(2) subst_literal(2) true_lit_simps(2))
qed

lemma interpretation_clause_congruence:
  assumes
    "clause.is_ground (clause \<cdot> \<gamma>)" 
    "upair ` I \<TTurnstile>l term.to_ground (Var var \<cdot>t \<gamma>) \<approx> term.to_ground update"
    "upair ` I \<TTurnstile> clause.to_ground (clause \<cdot> \<gamma>(var := update))"
  shows
    "upair ` I \<TTurnstile> clause.to_ground (clause \<cdot> \<gamma>)"
  using assms
proof(induction "clause")
  case empty
  then show ?case 
    by clause_simp
next
  case (add literal clause')

  have clause'_grounding: "clause.is_ground (clause' \<cdot> \<gamma>)"
    by (metis add.prems(1) clause_is_ground_add_mset subst_clause_add_mset)

  show ?case
  proof(cases "upair ` I \<TTurnstile> clause.to_ground (clause' \<cdot> \<gamma>(var := update))")
    case True
    show ?thesis 
      using add(1)[OF clause'_grounding assms(2) True]
      unfolding subst_clause_add_mset clause.to_ground_def
      by simp
  next
    case False
    then have "upair ` I \<TTurnstile>l literal.to_ground (literal \<cdot>l \<gamma>(var := update))"
      using add.prems
      by (metis (no_types, lifting) image_mset_add_mset subst_clause_add_mset clause.to_ground_def true_cls_add_mset)

    then have "upair ` I \<TTurnstile>l literal.to_ground (literal \<cdot>l \<gamma>)"
      using interpretation_literal_congruence add.prems
      by (metis clause_is_ground_add_mset subst_clause_add_mset)

    then show ?thesis 
      by (simp add: subst_clause_add_mset clause.to_ground_def)
  qed
qed

end
end

subsection \<open>Renaming\<close>

(* TODO: these work also without inj *)

context 
  fixes \<rho> :: "('f, 'v) subst"
  assumes renaming: "term_subst.is_renaming \<rho>"
begin

lemma renaming_vars_term:  "Var ` term.vars (term \<cdot>t \<rho>) = \<rho> ` (term.vars term)" 
proof(induction "term")
  case Var
  with renaming show ?case
    unfolding term_subst_is_renaming_iff
    by (metis Term.term.simps(17) eval_term.simps(1) image_empty image_insert is_VarE)
next
  case (Fun f terms)

  have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> term.vars (term \<cdot>t \<rho>)\<rbrakk> 
       \<Longrightarrow> Var x \<in> \<rho> ` \<Union> (term.vars ` set terms)"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  moreover have 
    "\<And>term x. \<lbrakk>term \<in> set terms; x \<in> term.vars term\<rbrakk>
       \<Longrightarrow> \<rho> x \<in> Var ` (\<Union>x' \<in> set terms. term.vars (x' \<cdot>t \<rho>))"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  ultimately show ?case
    by auto
qed

lemma renaming_vars_atom: "Var ` atom.vars (atom \<cdot>a \<rho>) = \<rho> ` atom.vars atom"
  unfolding atom.vars_def atom.subst_def 
  by(cases atom)(auto simp: image_Un renaming_vars_term)

lemma renaming_vars_literal: "Var ` literal.vars (literal \<cdot>l \<rho>) = \<rho> ` literal.vars literal"
  unfolding literal.vars_def literal.subst_def
  by(cases literal)(auto simp: renaming_vars_atom)

lemma renaming_vars_clause: "Var ` clause.vars (clause \<cdot> \<rho>) = \<rho> ` clause.vars clause"
  using renaming_vars_literal
  by(induction clause)(clause_auto simp: image_Un)

lemma surj_the_inv: "surj (\<lambda>x. the_inv \<rho> (Var x))"
  by (metis is_Var_def renaming surj_def term_subst_is_renaming_iff the_inv_f_f)

end

lemma needed: "surj g \<Longrightarrow> infinite {x. f x = ty} \<Longrightarrow> infinite {x. f (g x) = ty}"
  by (smt (verit) UNIV_I finite_imageI image_iff mem_Collect_eq rev_finite_subset subset_eq)

lemma obtain_ground_fun:
  assumes "term.is_ground t"
  obtains f ts where "t = Fun f ts"
  using assms
  by(cases t) auto

lemma vars_term_subst: "term.vars (t \<cdot>t \<sigma>) \<subseteq> term.vars t \<union> range_vars \<sigma>"
  by (meson Diff_subset order_refl subset_trans sup.mono vars_term_subst_apply_term_subset)

lemma vars_term_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "term.vars (t \<cdot>t \<mu>) \<subseteq> term.vars t \<union> term.vars s \<union> term.vars s'"
  using range_vars_subset_if_is_imgu[OF assms] vars_term_subst
  by fastforce

lemma vars_context_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "context.vars (c \<cdot>t\<^sub>c \<mu>) \<subseteq> context.vars c \<union> term.vars s \<union> term.vars s'"
  using  vars_term_imgu[OF assms]
  by (smt (verit, ccfv_threshold) Un_iff subset_iff subst_apply_term_ctxt_apply_distrib vars_term_ctxt_apply)

lemma vars_atom_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "atom.vars (a \<cdot>a \<mu>) \<subseteq> atom.vars a \<union> term.vars s \<union> term.vars s'"
  using vars_term_imgu[OF assms]
  unfolding atom.vars_def atom.subst_def 
  by(cases a) auto

lemma vars_literal_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "literal.vars (l \<cdot>l \<mu>) \<subseteq> literal.vars l \<union> term.vars s \<union> term.vars s'"
  using vars_atom_imgu[OF assms]
  unfolding literal.vars_def literal.subst_def set_literal_atm_of
  by (metis (no_types, lifting) UN_insert ccSUP_empty literal.map_sel sup_bot.right_neutral)

lemma vars_clause_imgu [clause_intro]:
  assumes "term_subst.is_imgu \<mu> {{s, s'}}"
  shows "clause.vars (c \<cdot> \<mu>) \<subseteq> clause.vars c \<union> term.vars s \<union> term.vars s'"
  using vars_literal_imgu[OF assms]
  unfolding clause.vars_def clause.subst_def
  by blast

end
