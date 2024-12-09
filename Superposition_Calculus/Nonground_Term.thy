theory Nonground_Term
 imports 
    Abstract_Substitution.Substitution_First_Order_Term
    Functional_Substitution_Lifting
    Ground_Term_Extra
begin

(* TODO *)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>Nonground Terms and Substitutions\<close>

type_synonym 'f ground_term = "'f gterm"

(* TODO: Already here with t or just from Nonground_Clause on?*)
notation subst_apply_term (infixl "\<cdot>t" 67)
notation subst_compose (infixl "\<odot>" 75)

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

lemma infinite_terms [intro]: "infinite (UNIV :: ('f, 'v) term set)"
proof-
  have "infinite (UNIV :: ('f, 'v) term list set)"
    using infinite_UNIV_listI.

  then have "\<And>f :: 'f. infinite ((Fun f) ` (UNIV :: ('f, 'v) term list set))"
    by (meson finite_imageD injI term.inject(2))

  then show "infinite (UNIV :: ('f, 'v) term set)"
    using infinite_super top_greatest by blast
qed

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

locale nonground_term = 
  base_functional_substitution +
  finite_variables +
  all_subst_ident_iff_ground + 
  renaming_variables +
  vars_subst

locale term_grounding =
  variables_in_base_imgu where base_vars = vars and base_subst = subst +
  grounding

global_interpretation "term": nonground_term where subst = "(\<cdot>t)" and  id_subst = Var and 
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
next
  fix \<rho> :: "('f, 'v) subst" and x
  assume "term_subst.is_renaming \<rho>"
  then show "\<rho> x \<in> range Var"
    unfolding is_Var_def term_subst_is_renaming_iff
    by blast
qed

hide_fact term.ground_subst_iff_base_ground_subst


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

lemma term_context_ground_iff_term_is_ground [simp]: "Term_Context.ground t = term.is_ground t"
  by(induction t) simp_all

declare Term_Context.ground_vars_term_empty [simp del]

lemma obtain_ground_fun:
  assumes "term.is_ground t"
  obtains f ts where "t = Fun f ts"
  using assms
  by(cases t) auto

lemma renaming_surj_the_inv: 
  fixes \<rho> :: "('f, 'v) subst"
  assumes "term_subst.is_renaming \<rho>"
  shows "surj (\<lambda>x. inv \<rho> (Var x))"
  using assms inv_f_f
  unfolding term_subst_is_renaming_iff is_Var_def surj_def
  by metis

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
