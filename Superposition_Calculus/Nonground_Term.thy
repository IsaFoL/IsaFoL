theory Nonground_Term
 imports 
    Abstract_Substitution.Substitution_First_Order_Term
    Functional_Substitution_Lifting
    Term_Rewrite_System
    Ground_Term_Extra
    Ground_Context
    HOL_Extra
    Multiset_Extra
    Entailment_Lifting
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>Nonground Terms and Substitutions\<close>

type_synonym 'f ground_term = "'f gterm"
type_synonym ('f, 'v) "context" = "('f, 'v) ctxt"

notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_compose (infixl "\<odot>" 75)

abbreviation subst_apply_ctxt ::
  "('f, 'v) context \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) context" (infixl "\<cdot>t\<^sub>c" 67) where
  "subst_apply_ctxt \<equiv> subst_apply_actxt"

lemma infinite_terms: "infinite (UNIV :: ('f, 'v) term set)"
proof-
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI.

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest by blast
qed


subsection\<open>Unified naming\<close>

locale vars_def =
  fixes vars_def :: "'expr \<Rightarrow> 'var" 
begin 

abbreviation "vars \<equiv> vars_def"

end

locale grounding_def = 
  fixes 
    to_ground_def :: "'expr \<Rightarrow> 'expr\<^sub>G" and
    from_ground_def :: "'expr\<^sub>G \<Rightarrow> 'expr"
begin 

abbreviation "to_ground \<equiv> to_ground_def"

abbreviation "from_ground \<equiv> from_ground_def"

end

global_interpretation "term": vars_def where vars_def = vars_term.

global_interpretation "term": grounding_def where 
  to_ground_def = gterm_of_term and from_ground_def = term_of_gterm .

subsection\<open>Term\<close>

lemma renaming_vars_term:
  assumes "\<forall>x. is_Var (\<rho> x)"
  shows "Var ` term.vars (t \<cdot>t \<rho>) = \<rho> ` (term.vars t)" 
proof(induction t)
  case Var
  with assms show ?case
    unfolding term_subst_is_renaming_iff
    by (metis Term.term.simps(17) eval_term.simps(1) image_empty image_insert is_VarE)
next
  case (Fun f terms)

  {
    fix t x
    assume "t \<in> set terms" "x \<in> term.vars (t \<cdot>t \<rho>)"

    then have "Var x \<in> \<rho> ` \<Union> (term.vars ` set terms)"
      using Fun
      by (smt (verit, del_insts) UN_iff image_UN image_eqI)
  }

  moreover { 
    fix t x
    assume "t \<in> set terms" "x \<in> term.vars t"

    then have "\<rho> x \<in> Var ` (\<Union>t' \<in> set terms. term.vars (t' \<cdot>t \<rho>))"
      using Fun
      by (smt (verit, del_insts) UN_iff image_UN image_eqI)
  }

  ultimately show ?case
    by auto
qed

locale "term" = 
  base_functional_substitution +
  finite_variables +
  all_subst_ident_iff_ground + 
  renaming_variables +
  vars_subst

locale term_grounding = 
  variables_in_base_imgu where base_vars = vars and base_subst = subst +
  grounding

global_interpretation "term": "term" where subst = "(\<cdot>t)" and  id_subst = Var and 
  comp_subst = "(\<odot>)" and
   vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set"  and subst_domain = subst_domain and 
   range_vars = range_vars
proof unfold_locales
  fix t :: "('f, 'v) term"  and \<sigma> \<tau> :: "('f, 'v) subst"
  assume "\<And>x. x \<in> term.vars t \<Longrightarrow> \<sigma> x = \<tau> x"
  then show "t \<cdot>t \<sigma> = t \<cdot>t \<tau>"
    by(rule term_subst_eq)
next
  fix t :: "('f, 'v) term"
  show "finite (term.vars t)"
    by simp
next
  fix t :: "('f, 'v) term"
  show "(term.vars t = {}) = (\<forall>\<sigma>. t \<cdot>t \<sigma> = t)"
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
  fix t :: "('f, 'v) term" and \<gamma> :: "('f, 'v) subst"

  show "term.vars (t \<cdot>t \<gamma>) = {} \<longleftrightarrow> (\<forall>x \<in> term.vars t. term.vars (\<gamma> x) = {})"
    using is_ground_iff.
next
  show "\<exists>t. term.vars t = {}"
    using vars_term_of_gterm
    by metis
next
  fix t :: "('f, 'v) term" and \<rho> :: "('f, 'v) subst"
  assume "term_subst.is_renaming \<rho>"

  then show "Var ` term.vars (t \<cdot>t \<rho>) = \<rho> ` term.vars t"
    unfolding term_subst_is_renaming_iff
    using renaming_vars_term
    by meson
next
  fix t :: "('f, 'v) term" and \<sigma>
  show "term.vars (t \<cdot>t \<sigma>) \<subseteq> term.vars t - subst_domain \<sigma> \<union> range_vars \<sigma>"
    by (rule vars_term_subst_apply_term_subset)  
qed

global_interpretation "term": term_grounding where subst = "(\<cdot>t)" and id_subst = Var and 
  comp_subst = "(\<odot>)" and vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" and 
  from_ground = term.from_ground and to_ground = term.to_ground
proof unfold_locales
   fix t :: "('f, 'v) term" and \<mu>  :: "('f, 'v) subst" and unifications

  assume imgu:
    "term_subst.is_imgu \<mu> unifications" 
    "\<forall>unification\<in>unifications. finite unification"
    "finite unifications" 

  show "term.vars (t \<cdot>t \<mu>) \<subseteq> term.vars t \<union> \<Union> (term.vars ` \<Union> unifications)"
    using range_vars_subset_if_is_imgu[OF imgu] vars_term_subst_apply_term_subset
    by fastforce
next
  {
    fix t :: "('f, 'v) term"
    assume t_is_ground: "term.is_ground t"

    have "\<exists>g. term.from_ground g = t"
    proof(intro exI)

      from t_is_ground 
      show "term.from_ground (term.to_ground t) = t"
        by(induction t)(simp_all add: map_idI)

    qed
  }

  then show "{t :: ('f, 'v) term. term.is_ground t} = range term.from_ground"
    by fastforce
next
  fix t\<^sub>G :: "('f) ground_term"
  show "term.to_ground (term.from_ground t\<^sub>G) = t\<^sub>G"
    by simp
qed

(* TODO: Simp? *)
lemma term_context_ground_iff_term_is_ground: "Term_Context.ground t = term.is_ground t"
  by(induction t) simp_all

lemma obtain_ground_fun:
  assumes "term.is_ground t"
  obtains f ts where "t = Fun f ts"
  using assms
  by(cases t) auto

lemma renaming_surj_the_inv: 
  fixes \<rho> :: "('f, 'v) subst"
  assumes "term_subst.is_renaming \<rho>"
  shows "surj (\<lambda>x. the_inv \<rho> (Var x))"
  using assms the_inv_f_f
  unfolding term_subst_is_renaming_iff is_Var_def surj_def
  by metis

subsection \<open>Entailment\<close>

lemma var_in_term:
  assumes "x \<in> term.vars t"
  obtains c where "t = c\<langle>Var x\<rangle>"
  using assms
proof(induction t)
  case Var
  then show ?case
    by (meson supteq_Var supteq_ctxtE)
next
  case (Fun f args)
  then obtain t' where "t' \<in> set args " "x \<in> term.vars t'"
    by (metis term.distinct(1) term.sel(4) term.set_cases(2))

  moreover then obtain args1 args2 where
    "args1 @ [t'] @ args2 = args"
    by (metis append_Cons append_Nil split_list)

  moreover then have "(More f args1 \<box> args2)\<langle>t'\<rangle> = Fun f args"
    by simp

  ultimately show ?case 
    using Fun(1)
    by (meson assms supteq_ctxtE that vars_term_supteq)
qed

lemma vars_term_ms_count:
  assumes "term.is_ground t"
  shows 
    "size {#x' \<in># vars_term_ms c\<langle>Var x\<rangle>. x' = x#} = Suc (size {#x' \<in># vars_term_ms c\<langle>t\<rangle>. x' = x#})"
  by(induction c)(auto simp: assms filter_mset_empty_conv)

locale term_entailment =
  fixes I :: "('f gterm \<times> 'f gterm) set"
  assumes 
    trans: "trans I" and
    sym: "sym I" and
    compatible_with_gctxt: "compatible_with_gctxt I"
begin

lemma symmetric_context_congruence:
  assumes "(t, t') \<in> I"
  shows "(c\<langle>t\<rangle>\<^sub>G, t'') \<in> I \<longleftrightarrow> (c\<langle>t'\<rangle>\<^sub>G, t'') \<in> I"
  by (meson assms compatible_with_gctxt compatible_with_gctxtD sym trans symD transE)

sublocale "term": symmetric_base_entailment where 
  vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
  subst = "(\<cdot>t)" and to_ground = term.to_ground and from_ground = term.from_ground
proof unfold_locales
  fix \<gamma> :: "('f, 'v) subst" and t t' update var

  assume 
    update_is_ground: "term.is_ground update" and
    var_grounding: "term.is_ground (\<gamma> var)" and
    var_update: "(term.to_ground (\<gamma> var), term.to_ground update) \<in> I" and
    term_grounding: "term.is_ground (t \<cdot>t \<gamma>)" and
    updated_term: "(term.to_ground (t \<cdot>t \<gamma>(var := update)), t') \<in> I"

  from term_grounding updated_term
  show "(term.to_ground (t \<cdot>t \<gamma>), t') \<in> I"
  proof(induction "size (filter_mset (\<lambda>var'. var' = var) (vars_term_ms t))" arbitrary: t)
    case 0

    then have "var \<notin> term.vars t"
      by (metis (mono_tags, lifting) filter_mset_empty_conv set_mset_vars_term_ms 
          size_eq_0_iff_empty)

    then have "t \<cdot>t \<gamma>(var := update) = t \<cdot>t \<gamma>"
      using term.subst_reduntant_upd 
      by (simp add: eval_with_fresh_var)

    with 0 show ?case
      by argo
  next
    case (Suc n)

    let ?context_to_ground = "map_args_actxt term.to_ground"

    have "var \<in> term.vars t"
      using Suc.hyps(2)
      by (metis (full_types) filter_mset_empty_conv nonempty_has_size set_mset_vars_term_ms 
          zero_less_Suc)

    then obtain c where t [simp]: "t = c\<langle>Var var\<rangle>"
      by (meson var_in_term)

    have [simp]: 
      "(?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G = term.to_ground (c\<langle>Var var\<rangle> \<cdot>t \<gamma>)"
      using Suc 
      by(induction c) simp_all

    have context_update [simp]: 
      "(?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground update\<rangle>\<^sub>G = term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>)"
      using Suc update_is_ground
      by(induction c) auto

    have "n = size {#var' \<in># vars_term_ms c\<langle>update\<rangle>. var' = var#}"
      using Suc vars_term_ms_count[OF update_is_ground, of var c]
      by auto

    moreover have "term.is_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>)"
      using Suc.prems update_is_ground 
      by auto

    moreover have "(term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>(var := update)), t') \<in> I"
      using Suc.prems update_is_ground
      by auto

    moreover have "(term.to_ground update, term.to_ground (\<gamma> var)) \<in> I"
      using var_update sym
      by (metis symD)

    moreover have "(term.to_ground (c\<langle>update\<rangle> \<cdot>t \<gamma>), t') \<in> I"
      using Suc calculation
      by blast

    ultimately have "((?context_to_ground (c \<cdot>t\<^sub>c \<gamma>))\<langle>term.to_ground (\<gamma> var)\<rangle>\<^sub>G, t') \<in> I"
      using symmetric_context_congruence context_update
      by metis

    then show ?case 
      by simp
  qed
qed (rule sym)

end

subsection\<open>Setup for lifting from terms\<close>

locale lifting = 
  based_functional_substitution_lifting + 
  all_subst_ident_iff_ground_lifting +
  grounding_lifting +
  renaming_variables_lifting +
  variables_in_base_imgu_lifting +
  vars_subst_lifting

locale lifting_from_term =
  lifting where comp_subst = "(\<odot>)" and id_subst = Var and subst_domain = subst_domain and 
  range_vars = range_vars and base_subst = "(\<cdot>t)" and base_vars = term.vars

end
