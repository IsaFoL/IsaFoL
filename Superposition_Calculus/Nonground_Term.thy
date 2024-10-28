theory Nonground_Term
 imports 
    Abstract_Substitution.Substitution_First_Order_Term
    Functional_Substitution
    Term_Rewrite_System
    Ground_Term_Extra
    Ground_Ctxt_Extra
    HOL_Extra
    Multiset_Extra
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67)

text \<open>Prefer @{thm [source] term_subst.subst_id_subst} to @{thm [source] subst_apply_term_empty}.\<close>
declare subst_apply_term_empty[no_atp]

section \<open>Nonground Terms and Substitutions\<close>

type_synonym 'f ground_term = "'f gterm"

type_synonym 'f ground_context = "'f gctxt"
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

global_interpretation "context": vars_def where 
  vars_def = "vars_ctxt".

global_interpretation "term": grounding_def where 
  to_ground_def = gterm_of_term and from_ground_def = term_of_gterm .

global_interpretation "context": grounding_def where 
  to_ground_def = gctxt_of_ctxt and from_ground_def = ctxt_of_gctxt.

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

  have "\<And>t x. \<lbrakk>t \<in> set terms; x \<in> term.vars (t \<cdot>t \<rho>)\<rbrakk> \<Longrightarrow> Var x \<in> \<rho> ` \<Union> (term.vars ` set terms)"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  moreover have 
    "\<And>t x. \<lbrakk>t \<in> set terms; x \<in> term.vars t\<rbrakk> \<Longrightarrow> \<rho> x \<in> Var ` (\<Union>t' \<in> set terms. term.vars (t' \<cdot>t \<rho>))"
    using Fun
    by (smt (verit, del_insts) UN_iff image_UN image_eqI)

  ultimately show ?case
    by auto
qed

global_interpretation
  "term": base_functional_substitution where 
  subst = subst_apply_term and id_subst = Var and comp_subst = "(\<odot>)" and 
  vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" +
  "term": finite_variables where vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" +
  "term": all_subst_ident_iff_ground where 
  is_ground = "term.is_ground :: ('f, 'v) term \<Rightarrow> bool" and subst = "(\<cdot>t)" + 
  "term": renaming_variables where vars = term.vars and is_renaming = term_subst.is_renaming and 
  id_subst = Var and subst = "(\<cdot>t)"
proof unfold_locales
  show "\<And>t \<sigma> \<tau>. (\<And>x. x \<in> term.vars t \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> t \<cdot>t \<sigma> = t \<cdot>t \<tau>"
    using term_subst_eq.
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
  show "\<And>\<gamma> t. (term.vars (t \<cdot>t \<gamma>) = {}) = (\<forall>x \<in> term.vars t. term.vars (\<gamma> x) = {})"
    by (meson is_ground_iff)
next
  show "\<exists>t. term.vars t = {}"
    by (meson vars_term_of_gterm)
next
  show "\<And>t \<rho>. term_subst.is_renaming \<rho> \<Longrightarrow> Var ` term.vars (t \<cdot>t \<rho>) = \<rho> ` term.vars t"
    by (meson renaming_vars_term term_subst_is_renaming_iff)
qed

global_interpretation
  "term": grounding where 
  vars = "term.vars :: ('f, 'v) term \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
  subst = "(\<cdot>t)" and to_ground = term.to_ground and from_ground = term.from_ground
proof unfold_locales
  have "\<And>t :: ('f, 'v) term. term.is_ground t \<Longrightarrow> \<exists>g. term.from_ground g = t"
  proof(intro exI)
    fix t :: "('f, 'v) term"
    assume "term.is_ground t"
    then show "term.from_ground (term.to_ground t) = t"
      by(induction t)(simp_all add: map_idI)
  qed

  then show "{t :: ('f, 'v) term. term.is_ground t} = range term.from_ground"
    by fastforce
next
  show "\<And>t\<^sub>G. term.to_ground (term.from_ground t\<^sub>G) = t\<^sub>G"
    by simp
qed

lemma term_context_ground_iff_term_is_ground: "Term_Context.ground t = term.is_ground t"
  by(induction t) simp_all

subsection\<open>Context\<close>

(* TODO: Try how much can be generalized using abstract contexts *)
global_interpretation "context": all_subst_ident_iff_ground where 
  is_ground = "\<lambda>c. context.vars c = {}" and subst = "(\<cdot>t\<^sub>c)"
proof unfold_locales
  fix c :: "('f, 'v) context"
  show "context.vars c = {} = (\<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c)"
  proof (intro iffI)
    show "context.vars c = {} \<Longrightarrow> \<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"
      by(induction c) (simp_all add: list.map_ident_strong)
  next
    assume "\<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"

    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> \<forall>\<sigma>. c\<langle>t\<^sub>G\<rangle> \<cdot>t \<sigma> = c\<langle>t\<^sub>G\<rangle>"
      by simp

    then have "\<And>t\<^sub>G. term.is_ground t\<^sub>G \<Longrightarrow> term.is_ground c\<langle>t\<^sub>G\<rangle>"
      by (meson is_ground_trm_iff_ident_forall_subst)

    then show "context.vars c = {}"
      by (metis sup.commute sup_bot_left vars_term_ctxt_apply vars_term_of_gterm)
  qed
next
  fix c :: "('f, 'v) context" and cs :: "('f, 'v) context set"
  assume finite: "finite cs" and non_ground: "context.vars c \<noteq> {}"

  then show "\<exists>\<sigma>. c \<cdot>t\<^sub>c \<sigma> \<noteq> c \<and> c \<cdot>t\<^sub>c \<sigma> \<notin> cs"
  proof(induction c arbitrary: cs)
    case Hole
    then show ?case
      by simp
  next
    case (More f ts c ts')

    show ?case
    proof(cases "context.vars c = {}")
      case True

      let ?sub_terms = 
        "\<lambda>\<kappa> :: ('f, 'v) context. case \<kappa> of More _ ts _ ts' \<Rightarrow> set ts \<union> set ts'  | _ \<Rightarrow> {}"

      let ?cs' = "set ts \<union> set ts' \<union> \<Union>(?sub_terms ` cs)"

      from True obtain t where t: "t \<in> set ts \<union> set ts'" and non_ground: "\<not>term.is_ground t"
        using More.prems by auto

      have "\<And>\<kappa>. finite (?sub_terms \<kappa>)"
      proof-  
        fix c
        show "finite (?sub_terms c)"
          by(cases c) simp_all
      qed

      then have "finite (\<Union>(?sub_terms ` cs))"
        using More.prems(1) by blast

      then have finite: "finite ?cs'"
        by blast

      obtain \<sigma> where \<sigma>: "t \<cdot>t \<sigma> \<noteq> t" and cs': "t \<cdot>t \<sigma> \<notin> ?cs'"
        using term.exists_non_ident_subst[OF finite non_ground]
        by blast

      then have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts c ts'"
        using t set_map_id[of _  _ "\<lambda>t. t \<cdot>t \<sigma>"]
        by auto

      moreover have " More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<notin> cs"
        using cs' t
        by auto

      ultimately show ?thesis
        by blast
    next
      case False

      let ?sub_contexts = "(\<lambda>\<kappa>. case \<kappa> of More _ _ \<kappa> _ \<Rightarrow> \<kappa>) ` {\<kappa> \<in> cs. \<kappa> \<noteq> \<box>}"

      have "finite ?sub_contexts"
        using More.prems(1)
        by auto

      then obtain \<sigma> where \<sigma>: "c \<cdot>t\<^sub>c \<sigma> \<noteq> c" and sub_contexts: "c \<cdot>t\<^sub>c \<sigma> \<notin> ?sub_contexts"
        using More.IH[OF _ False]
        by blast

      then have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<noteq> More f ts c ts'"
        by simp

      moreover have "More f ts c ts' \<cdot>t\<^sub>c \<sigma> \<notin> cs"
        using sub_contexts image_iff
        by fastforce

      ultimately show ?thesis 
        by blast
    qed
  qed
qed

global_interpretation "context": based_functional_substitution where
  subst = "(\<cdot>t\<^sub>c)" and vars = context.vars and id_subst = Var and comp_subst = "(\<odot>)" and 
  base_vars = term.vars and base_subst = "(\<cdot>t)"
proof(unfold_locales, unfold substitution_ops.is_ground_subst_def)
  fix c :: "('f, 'v) context"
  show "c \<cdot>t\<^sub>c Var = c"
    by (induction c) auto
next
  show "\<And>c \<sigma> \<tau>. c \<cdot>t\<^sub>c \<sigma> \<odot> \<tau> = c \<cdot>t\<^sub>c \<sigma> \<cdot>t\<^sub>c \<tau>"
    by simp
next
  show "\<And>c. context.vars c = {} \<Longrightarrow> \<forall>\<sigma>. c \<cdot>t\<^sub>c \<sigma> = c"
    using context.all_subst_ident_iff_ground by blast
next 
  show "\<And>c \<sigma> \<tau>. (\<And>x. x \<in> context.vars c \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> c \<cdot>t\<^sub>c \<sigma> = c \<cdot>t\<^sub>c \<tau>"
    using ctxt_subst_eq.
next
  fix \<gamma> :: "('f,'v) subst"

  show "(\<forall>c. context.vars (c \<cdot>t\<^sub>c \<gamma>) = {}) \<longleftrightarrow> (\<forall>t. term.vars (t \<cdot>t \<gamma>) = {})"
  proof(intro iffI allI equals0I)
    fix t x

    assume is_ground: "\<forall>c. context.vars (c \<cdot>t\<^sub>c \<gamma>) = {}" and vars: "x \<in> term.vars (t \<cdot>t \<gamma>)"

    have "\<And>f. context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>) = {}"
      using is_ground
      by presburger

    moreover have "\<And>f. x \<in> context.vars (More f [t] Hole [] \<cdot>t\<^sub>c \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  next
    fix c x
    assume is_ground: "\<forall>t. term.is_ground (t \<cdot>t \<gamma>)" and vars: "x \<in> context.vars (c \<cdot>t\<^sub>c \<gamma>)"

    have "\<And>t. term.is_ground (c\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using is_ground
      by presburger

    moreover have "\<And>t. x \<in> term.vars (c\<langle>t\<rangle> \<cdot>t \<gamma>)"
      using vars
      by simp

    ultimately show False
      by blast
  qed
next
  fix c and \<gamma> :: "('f, 'v) subst"

  show "context.vars (c \<cdot>t\<^sub>c \<gamma>) = {} \<longleftrightarrow> (\<forall>x \<in> context.vars c. term.is_ground (\<gamma> x))"
    by(induction c)(auto simp: term.is_grounding_iff_vars_grounded)
qed

global_interpretation "context": finite_variables 
  where vars = "context.vars :: ('f, 'v) context \<Rightarrow> 'v set"
proof unfold_locales
  fix c :: "('f, 'v) context"

  have "\<And>t. finite (term.vars c\<langle>t\<rangle>)"
    using term.finite_vars by blast

  then show "finite (context.vars c)"
    unfolding vars_term_ctxt_apply finite_Un
    by simp
qed

global_interpretation "context": grounding where 
  vars = "context.vars :: ('f, 'v) context \<Rightarrow> 'v set" and id_subst = Var and comp_subst = "(\<odot>)" and 
  subst = "(\<cdot>t\<^sub>c)" and from_ground = context.from_ground and to_ground = context.to_ground
proof unfold_locales
  have "\<And>c. context.vars c = {} \<Longrightarrow> \<exists>c\<^sub>G. context.from_ground c\<^sub>G = c"
    by (metis Un_empty_left gctxt_of_ctxt_inv term.ground_exists term.to_ground_inverse 
        term_of_gterm_ctxt_apply_ground(1) vars_term_ctxt_apply)

  then show "{c. context.vars c = {}} = range context.from_ground"
    by force
next 
  show "\<And>c\<^sub>G. context.to_ground (context.from_ground c\<^sub>G) = c\<^sub>G"
    by simp
qed

global_interpretation "context": renaming_variables where vars = context.vars and 
  is_renaming = context.is_renaming and id_subst = Var and subst = "(\<cdot>t\<^sub>c)"
proof unfold_locales
  fix c and \<rho> :: "('f, 'v) subst"
  assume "context.is_renaming \<rho>" 
  then have "\<And>t. Var ` term.vars (c\<langle>t\<rangle> \<cdot>t \<rho>) = \<rho> ` term.vars c\<langle>t\<rangle>"
    by (meson term.renaming_variables)
  
  then show "Var ` context.vars (c \<cdot>t\<^sub>c \<rho>) = \<rho> ` context.vars c"
    unfolding vars_term_ctxt_apply subst_apply_term_ctxt_apply_distrib
    by (metis Un_commute Un_empty_left is_ground_trm_iff_ident_forall_subst term.ground_exists)
qed

lemma ground_ctxt_iff_context_is_ground: "ground_ctxt c \<longleftrightarrow> context.is_ground c"
  by(induction c)(simp_all add: term_context_ground_iff_term_is_ground)

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

lemma renaming_surj_the_inv: 
  fixes \<rho> :: "('f, 'v) subst"
  assumes "term_subst.is_renaming \<rho>"
  shows "surj (\<lambda>x. the_inv \<rho> (Var x))"
  using assms the_inv_f_f
  unfolding term_subst_is_renaming_iff is_Var_def surj_def
  by metis
                    
end
