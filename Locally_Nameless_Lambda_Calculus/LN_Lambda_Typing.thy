theory LN_Lambda_Typing
  imports
    "HOL-Library.Dlist"
    LN_Lambda_Term
    "Abstract_Substitution.Substitution"
begin

abbreviation fold2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c \<Rightarrow> 'c" where
  "fold2 f xs ys \<equiv> fold (\<lambda>(x, y). f x y) (zip xs ys)"

definition fun_upds :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "fun_upds f xs ys = fold2 (\<lambda>x y f. f(x := y)) xs ys f"

class arity =
  fixes arity :: "'a \<Rightarrow> nat"

class term_signature =
  fixes
    True_tconst :: 'a and
    False_tconst :: 'a and
    Neg_tconst :: 'a and
    Conj_tconst :: 'a and
    Disj_tconst :: 'a and
    Imp_tconst :: 'a and
    Eq_tconst :: 'a and
    Neq_tconst :: 'a

class type_signature = arity +
  fixes bool_tyctr :: 'a and fun_tyctr :: 'a
  assumes arity\<^sub>_tyctr_simps[simp]: "arity bool_tyctr = 0" "arity fun_tyctr = 2"


section \<open>Pretypes\<close>

datatype (type_vars_prety: '\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety =
  PretyVar '\<V>\<^sub>t\<^sub>y |
  PretyCtr '\<Sigma>\<^sub>t\<^sub>y "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety list"


subsection \<open>Substitutions\<close>

primrec subst_prety ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety \<Rightarrow> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" where
  "subst_prety (PretyVar x) \<sigma> = \<sigma> x" |
  "subst_prety (PretyCtr \<kappa> \<tau>s) \<sigma> = PretyCtr \<kappa> (map (\<lambda>\<tau>. subst_prety \<tau> \<sigma>) \<tau>s)"

lemma subst_prety_PretyVar[simp]: "subst_prety \<tau> PretyVar = \<tau>"
proof (induction \<tau>)
  case (PretyVar x)
  then show ?case
    by simp
next
  case (PretyCtr \<kappa> \<tau>s)
  then show ?case
    by (simp add: list.map_ident_strong)
qed

definition comp_subst_prety ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety) \<Rightarrow> '\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" where
  "comp_subst_prety \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<equiv> \<lambda>x. subst_prety (\<sigma>\<^sub>1 x) \<sigma>\<^sub>2"

global_interpretation comp_subst_prety: monoid comp_subst_prety PretyVar
proof unfold_locales
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  show "comp_subst_prety (comp_subst_prety \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 = comp_subst_prety \<sigma>\<^sub>1 (comp_subst_prety \<sigma>\<^sub>2 \<sigma>\<^sub>3)"
    unfolding comp_subst_prety_def
  proof (intro ext)
    have "subst_prety (subst_prety t \<sigma>\<^sub>2) \<sigma>\<^sub>3 = subst_prety t (\<lambda>x. subst_prety (\<sigma>\<^sub>2 x) \<sigma>\<^sub>3)" for t
    proof (induction t)
      case (PretyVar y)
      then show ?case
        by (metis subst_prety.simps(1))
    next
      case (PretyCtr \<kappa> \<tau>s)
      then show ?case
        unfolding subst_prety.simps prety.inject
        unfolding list.map_comp comp_def
        by simp
    qed
    then show "\<And>x. subst_prety (subst_prety (\<sigma>\<^sub>1 x) \<sigma>\<^sub>2) \<sigma>\<^sub>3 =
      subst_prety (\<sigma>\<^sub>1 x) (\<lambda>x. subst_prety (\<sigma>\<^sub>2 x) \<sigma>\<^sub>3)"
      by metis
  qed
next
  show "\<And>a. comp_subst_prety PretyVar a = a"
    by (simp add: comp_subst_prety_def)
next
  show "\<And>a. comp_subst_prety a PretyVar = a"
    by (simp add: comp_subst_prety_def)
qed

global_interpretation subst_prety: substitution where
  comp_subst = comp_subst_prety and
  id_subst = PretyVar and
  subst = subst_prety and
  is_ground = "\<lambda>\<tau>. type_vars_prety \<tau> = {}"
proof unfold_locales
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  show "subst_prety \<tau> (comp_subst_prety \<sigma>\<^sub>1 \<sigma>\<^sub>2) = subst_prety (subst_prety \<tau> \<sigma>\<^sub>1) \<sigma>\<^sub>2"
    by (induction \<tau>) (simp_all add: comp_subst_prety_def)
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  show "subst_prety \<tau> PretyVar = \<tau>"
    by simp
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  assume "type_vars_prety \<tau> = {}"
  then show "\<forall>\<sigma>. subst_prety \<tau> \<sigma> = \<tau>"
    by (induction \<tau>) (simp_all add: list.map_ident_strong)
qed
                                                            
section \<open>Well-Formed Types\<close>

inductive wf_prety :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) prety \<Rightarrow> bool" where
  PretyVar: "wf_prety (PretyVar \<alpha>)"
    for \<alpha> :: '\<V>\<^sub>t\<^sub>y |
  PretyCtr: "wf_prety (PretyCtr \<kappa> \<tau>s)"
    if "length \<tau>s = arity \<kappa>" and "\<forall>\<tau> \<in> set \<tau>s. wf_prety \<tau>"
    for \<kappa> :: '\<Sigma>\<^sub>t\<^sub>y and \<tau>s :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety list"

typedef (overloaded) ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty = \<open>{\<tau> :: ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety. wf_prety \<tau>}\<close>
  morphisms Rep_ty Abs_ty
proof
  show \<open>PretyVar undefined \<in> {\<tau>. wf_prety \<tau>}\<close>
    by (blast intro: wf_prety.intros)
qed

setup_lifting type_definition_ty

lift_definition TyVar :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" is PretyVar
  by (rule wf_prety.PretyVar)

definition TyCtr :: "'\<Sigma>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty list \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" where
  "TyCtr \<kappa> \<tau>s = Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s))"

lemma wf_prety_PretyCtr:
  assumes "length \<tau>s = arity \<kappa>"
  shows "wf_prety (PretyCtr \<kappa> (map Rep_ty \<tau>s))"
proof (rule wf_prety.PretyCtr)
  show "\<forall>\<tau>\<in>set (map Rep_ty \<tau>s). wf_prety \<tau>"
    using Rep_ty by auto
qed (use assms in simp_all)


subsection \<open>Injection\<close>

lemma ty_inject[simp]:
  "TyVar x = TyVar y \<longleftrightarrow> x = y"
  "length \<tau>s\<^sub>1 = arity \<kappa>\<^sub>1 \<Longrightarrow> length \<tau>s\<^sub>2 = arity \<kappa>\<^sub>2 \<Longrightarrow>
    TyCtr \<kappa>\<^sub>1 \<tau>s\<^sub>1 = TyCtr \<kappa>\<^sub>2 \<tau>s\<^sub>2 \<longleftrightarrow> \<kappa>\<^sub>1 = \<kappa>\<^sub>2 \<and> \<tau>s\<^sub>1 = \<tau>s\<^sub>2"
proof -
  show "TyVar x = TyVar y \<longleftrightarrow> x = y"
    by (metis TyVar.rep_eq prety.inject(1))
  show "length \<tau>s\<^sub>1 = arity \<kappa>\<^sub>1 \<Longrightarrow> length \<tau>s\<^sub>2 = arity \<kappa>\<^sub>2 \<Longrightarrow>
    TyCtr \<kappa>\<^sub>1 \<tau>s\<^sub>1 = TyCtr \<kappa>\<^sub>2 \<tau>s\<^sub>2 \<longleftrightarrow> \<kappa>\<^sub>1 = \<kappa>\<^sub>2 \<and> \<tau>s\<^sub>1 = \<tau>s\<^sub>2"
    unfolding TyCtr_def
    by (metis Abs_ty_inject[of "PretyCtr \<kappa>\<^sub>2 (map Rep_ty \<tau>s\<^sub>2)" "PretyCtr \<kappa>\<^sub>1 (map Rep_ty \<tau>s\<^sub>1)"]
        Rep_ty_inject list.inj_map_strong[of \<tau>s\<^sub>1 \<tau>s\<^sub>2 Rep_ty Rep_ty] mem_Collect_eq prety.inject(2)
        wf_prety_PretyCtr)
qed

subsection \<open>Induction and Cases rules\<close>

lemma ty_induct [case_names TyVar TyCtr, induct type: ty]:
  assumes
    TyVar_case: "\<And>x. P (TyVar x)" and
    TyCtr_case: "\<And>\<kappa> \<tau>s. length \<tau>s = arity \<kappa> \<Longrightarrow> (\<And>\<tau>. \<tau> \<in> set \<tau>s \<Longrightarrow> P \<tau>) \<Longrightarrow> P (TyCtr \<kappa> \<tau>s)"
  shows "P x"
proof (cases x)
  case (Abs_ty \<tau>)
  then have "wf_prety \<tau>"
    by simp
  then show ?thesis
    unfolding \<open>x = Abs_ty \<tau>\<close>
  proof (induction \<tau>)
    case (PretyVar y)
    show ?case
      unfolding TyVar.abs_eq[symmetric]
      using TyVar_case .
  next
    case (PretyCtr \<kappa> \<tau>s)

    have "P (Abs_ty (PretyCtr \<kappa> (map Rep_ty (map Abs_ty \<tau>s))))"
    proof (rule TyCtr_case[unfolded TyCtr_def])
      show "length (map Abs_ty \<tau>s) = arity \<kappa>"
        by (simp add: PretyCtr.hyps)
    next
      show "\<And>\<tau>. \<tau> \<in> set (map Abs_ty \<tau>s) \<Longrightarrow> P \<tau>"
        using PretyCtr.IH by auto
    qed

    moreover have "map Rep_ty (map Abs_ty \<tau>s) = \<tau>s"
      unfolding list.map_comp comp_def
    proof (rule list.map_ident_strong)
      show "\<And>z. z \<in> set \<tau>s \<Longrightarrow> Rep_ty (Abs_ty z) = z"
        by (simp add: Abs_ty_inverse PretyCtr.IH)
    qed

    ultimately show ?case
      by metis
  qed
qed

lemma ty_exhaust [case_names TyVar TyCtr]:
  assumes
    TyVar_case: "\<And>x. \<tau> = TyVar x \<Longrightarrow> thesis" and
    TyCtr_case: "\<And>\<kappa> \<tau>s. \<tau> = TyCtr \<kappa> \<tau>s \<Longrightarrow> length \<tau>s = arity \<kappa> \<Longrightarrow> thesis"
  shows thesis
  using assms
  by (induction \<tau>) metis+


subsection \<open>Type Variables\<close>

lift_definition type_vars :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty \<Rightarrow> '\<V>\<^sub>t\<^sub>y set"
  is type_vars_prety .

lemma type_vars_TyVar[simp]: "type_vars (TyVar x) = {x}"
  by (simp add: TyVar.rep_eq type_vars.rep_eq)

lemma type_vars_TyCtr[simp]:
  "length \<tau>s = arity \<kappa> \<Longrightarrow> type_vars (TyCtr \<kappa> \<tau>s) = (\<Union>\<tau> \<in> set \<tau>s. type_vars \<tau>)"
  by (simp add: Abs_ty_inverse TyCtr_def type_vars_def wf_prety_PretyCtr)


subsection \<open>Common Types\<close>

lemma wf_prety_PretyCtr_bool_tyctr[intro]: "wf_prety (PretyCtr bool_tyctr [])"
  by (rule wf_prety.PretyCtr) simp_all

definition TyBool :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty" where
  "TyBool \<equiv> Abs_ty (PretyCtr bool_tyctr [])"


lemma wf_prety_PretyCtr_fun_tyctr[intro]: "wf_prety (PretyCtr fun_tyctr [Rep_ty \<tau>\<^sub>1, Rep_ty \<tau>\<^sub>2])"
proof (intro wf_prety.PretyCtr[rule_format])
  show "\<And>x. x \<in> set [Rep_ty \<tau>\<^sub>1, Rep_ty \<tau>\<^sub>2] \<Longrightarrow> wf_prety x"
    using Rep_ty by auto
qed simp_all

definition TyFun ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty" where
  "TyFun \<tau>\<^sub>1 \<tau>\<^sub>2 \<equiv> Abs_ty (PretyCtr fun_tyctr [Rep_ty \<tau>\<^sub>1, Rep_ty \<tau>\<^sub>2])"


subsection \<open>Substitutions\<close>

lift_definition subst_ty ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty \<Rightarrow> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty" (infix "\<cdot>\<^sub>t\<^sub>y" 55)
  is subst_prety
proof -
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and \<sigma> :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  assume "wf_prety \<tau>" and "\<And>x. wf_prety (\<sigma> x)"
  then show "wf_prety (subst_prety \<tau> \<sigma>)"
    by (induction \<tau> rule: wf_prety.induct) (simp_all add: wf_prety.PretyCtr)
qed

lemma subst_ty_simps[simp]:
  "TyVar x \<cdot>\<^sub>t\<^sub>y \<sigma> = \<sigma> x"
  "length \<tau>s = arity \<kappa> \<Longrightarrow> TyCtr \<kappa> \<tau>s \<cdot>\<^sub>t\<^sub>y \<sigma> = TyCtr \<kappa> (map (\<lambda>\<tau>. \<tau> \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>s)"
proof -
  show "TyVar x \<cdot>\<^sub>t\<^sub>y \<sigma> = \<sigma> x"
    by (metis Rep_ty_inject TyVar.rep_eq comp_def id_apply subst_prety.simps(1) subst_ty.rep_eq)
  show "length \<tau>s = arity \<kappa> \<Longrightarrow> TyCtr \<kappa> \<tau>s \<cdot>\<^sub>t\<^sub>y \<sigma> = TyCtr \<kappa> (map (\<lambda>\<tau>. \<tau> \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>s)"
    by (smt (verit, best) Abs_ty_inverse Rep_ty_inverse
        TyCtr_def list.map_comp map_eq_conv
        mem_Collect_eq o_def subst_prety.simps(2)
        subst_ty.rep_eq wf_prety_PretyCtr)
qed

lemma subst_ty_TyVar[simp]: "\<tau> \<cdot>\<^sub>t\<^sub>y TyVar = \<tau>"
  by (induction \<tau> rule: ty_induct) (simp_all add: list.map_ident_strong)

lift_definition comp_subst_ty ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) \<Rightarrow> '\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty"
  (infix "\<circ>\<^sub>t\<^sub>y" 50) is comp_subst_prety
  by (metis (no_types, lifting) rel_fun_eq_rel[of "eq_onp wf_prety"] eq_onp_same_args[of wf_prety]
      subst_ty.rsp
      rel_funD2[of "rel_fun (=) (eq_onp wf_prety)" "eq_onp wf_prety" "subst_prety _"
        "subst_prety _"]
      rel_funD2[of "eq_onp wf_prety" "rel_fun (rel_fun (=) (eq_onp wf_prety)) (eq_onp wf_prety)"
        subst_prety subst_prety]
      comp_subst_prety_def)

lemma comp_subst_ty_conv: "\<sigma>\<^sub>1 \<circ>\<^sub>t\<^sub>y \<sigma>\<^sub>2 = (\<lambda>x. \<sigma>\<^sub>1 x \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>2)"
  by (metis (mono_tags, opaque_lifting)
      Rep_ty_inverse
      subst_ty.rep_eq[of "\<sigma>\<^sub>1 _" \<sigma>\<^sub>2]
      comp_subst_ty.rep_eq[of \<sigma>\<^sub>1 \<sigma>\<^sub>2]
      comp_id[of "Rep_ty \<circ> _"]
      comp_apply[of Rep_ty]
      comp_subst_prety_def[of "Rep_ty \<circ> \<sigma>\<^sub>1" "Rep_ty \<circ> \<sigma>\<^sub>2"])

global_interpretation comp_subst_ty: monoid comp_subst_ty TyVar
proof unfold_locales
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty"
  show "((\<sigma>\<^sub>1 \<circ>\<^sub>t\<^sub>y \<sigma>\<^sub>2) \<circ>\<^sub>t\<^sub>y \<sigma>\<^sub>3) = (\<sigma>\<^sub>1 \<circ>\<^sub>t\<^sub>y (\<sigma>\<^sub>2 \<circ>\<^sub>t\<^sub>y \<sigma>\<^sub>3))"
    unfolding comp_subst_ty_conv
  proof (intro ext)
    have "(t \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>2) \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>3 = t \<cdot>\<^sub>t\<^sub>y (\<lambda>x. \<sigma>\<^sub>2 x \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>3)" for t
      by (induction t) simp_all

    then show "\<And>x. (\<sigma>\<^sub>1 x \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>2) \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>3 = \<sigma>\<^sub>1 x \<cdot>\<^sub>t\<^sub>y (\<lambda>x. \<sigma>\<^sub>2 x \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>3)"
      by metis
  qed
next
  show "\<And>a. (TyVar \<circ>\<^sub>t\<^sub>y a) = a"
    by (simp add: comp_subst_ty_conv)
next
  show "\<And>a. (a \<circ>\<^sub>t\<^sub>y TyVar) = a"
    by (simp add: comp_subst_ty_conv)
qed


global_interpretation subst_ty: substitution where
  comp_subst = comp_subst_ty and
  id_subst = TyVar and
  subst = subst_ty and
  is_ground = "\<lambda>\<tau>. type_vars \<tau> = {}"
proof unfold_locales
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"
  show "\<tau> \<cdot>\<^sub>t\<^sub>y (\<sigma>\<^sub>1 \<circ>\<^sub>t\<^sub>y \<sigma>\<^sub>2) = (\<tau> \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>1) \<cdot>\<^sub>t\<^sub>y \<sigma>\<^sub>2"
    by (induction \<tau>) (simp_all add: comp_subst_ty_conv)
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty"
  show "subst_ty \<tau> TyVar = \<tau>"
    by simp
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty"
  assume "type_vars \<tau> = {}"
  then show "\<forall>\<sigma>. \<tau> \<cdot>\<^sub>t\<^sub>y \<sigma> = \<tau>"
    by (induction \<tau>) (simp_all add: list.map_ident_strong)
qed

section \<open>Type System\<close>

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty = "'\<V>\<^sub>t\<^sub>y dlist \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty list \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"

inductive has_type ::
  "('\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) const_ty) \<Rightarrow> ('\<V> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty) \<Rightarrow>
    (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty \<Rightarrow> bool"
  for \<C> where
  Const: "has_type \<C> \<F> (Const c \<tau>\<^sub>1s ts) \<tau>"
    if "\<C> c = (\<alpha>s, \<tau>\<^sub>2s, \<tau>\<^sub>3)" and "Dlist.length \<alpha>s = length \<tau>\<^sub>1s" and
      "\<sigma> = fun_upds TyVar (list_of_dlist \<alpha>s) \<tau>\<^sub>1s" and
      "list_all2 (has_type \<C> \<F>) ts (map (\<lambda>\<tau>\<^sub>2. \<tau>\<^sub>2 \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>\<^sub>2s)" and
      "\<tau> = \<tau>\<^sub>3 \<cdot>\<^sub>t\<^sub>y \<sigma>"
    for \<F> :: "'\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) const_ty" and c \<tau>\<^sub>1s ts \<tau> |
  Free: "has_type \<C> \<F> (Free f) \<tau>"
    if "\<F> f = \<tau>"
    for \<F> f \<tau> |
  App: "has_type \<C> \<F> (App t\<^sub>1 t\<^sub>2) \<tau>\<^sub>2"
    if "has_type \<C> \<F> t\<^sub>1 (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)" and "has_type \<C> \<F> t\<^sub>2 \<tau>\<^sub>1"
    for \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 |
  Abs: "has_type \<C> \<F> (Abs \<tau>\<^sub>1 t) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> has_type \<C> (\<F>(x := \<tau>\<^sub>1)) (subst_bound 0 (Free x) t) \<tau>\<^sub>2"
    for \<F> t \<tau>\<^sub>1 \<tau>\<^sub>2 \<X>

lemma locally_closed_if_has_type[intro]: "has_type \<C> \<F> t \<tau> \<Longrightarrow> locally_closed t"
proof (induction \<F> t \<tau> rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 \<alpha>s \<tau>\<^sub>2s)
  show ?case
  proof (rule locally_closed.Const)
    show "list_all locally_closed ts"
      using Const.IH
      by (simp add: list_all2_conv_all_nth list_all_length)
  qed
qed (auto intro: locally_closed.intros)

lemma has_type_weaken_funenv:
  "has_type \<C> \<F> t \<tau>\<^sub>1 \<Longrightarrow> x \<notin> free_vars t \<Longrightarrow> has_type \<C> (\<F>(x := \<tau>\<^sub>2)) t \<tau>\<^sub>1"
proof (induction \<F> t \<tau>\<^sub>1 rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau> \<alpha>s \<tau>\<^sub>2s \<tau>\<^sub>3 \<sigma>)
  show ?case
  proof (rule has_type.Const)
    show "list_all2 (has_type \<C> (\<F>(x := \<tau>\<^sub>2))) ts (map (\<lambda>\<tau>\<^sub>2. \<tau>\<^sub>2 \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>\<^sub>2s)"
      by (rule list.rel_mono_strong[OF Const.IH]) (use Const.prems in force)
  qed (use Const in simp_all)
next
  case (Free \<F> f \<tau>)
  then show ?case
    by (simp add: has_type.Free)
next
  case (App \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (Abs \<F> t \<tau>\<^sub>1 \<tau>\<^sub>3 \<X>)
  show ?case
  proof (rule has_type.Abs)
    fix y
    assume "y |\<notin>| \<X>"
    show "has_type \<C> (\<F>(x := \<tau>\<^sub>2, y := \<tau>\<^sub>1)) (subst_bound 0 (Free y) t) \<tau>\<^sub>3"
    proof (cases "x = y")
      case True

      then have "\<F>(x := \<tau>\<^sub>2, y := \<tau>\<^sub>1) = \<F>(y := \<tau>\<^sub>1)"
        by simp

      then show ?thesis
        using Abs.hyps \<open>y |\<notin>| \<X>\<close> by metis
    next
      case False

      then have "\<F>(x := \<tau>\<^sub>2, y := \<tau>\<^sub>1) = \<F>(y := \<tau>\<^sub>1, x := \<tau>\<^sub>2)"
        by auto

      moreover have "x \<notin> free_vars (subst_bound 0 (Free y) t)"
        using \<open>x \<notin> free_vars (Abs \<tau>\<^sub>1 t)\<close>[simplified] \<open>x \<noteq> y\<close>
        using free_vars_subst_bound_subset by force

      ultimately show ?thesis
        using Abs.IH[OF \<open>y |\<notin>| \<X>\<close>] by metis
    qed
  qed
qed

lemma has_type_subst_free:
  fixes t :: "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty, '\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V>\<^sub>t\<^sub>y set)"
  assumes "has_type \<C> \<F> t \<tau>\<^sub>1" and "\<F> x = \<tau>\<^sub>2" and "has_type \<C> \<F> u \<tau>\<^sub>2"
  shows "has_type \<C> \<F> (subst_free x u t) \<tau>\<^sub>1"
  using assms(2-4)
proof (induction \<F> t \<tau>\<^sub>1 rule: has_type.induct)
  case (Const \<F> c \<tau>\<^sub>1s ts \<tau>\<^sub>3 \<alpha>s \<tau>\<^sub>2s)
  then show ?case
    by (simp add: has_type.Const list_all2_mono)
next
  case (Free \<F> f \<tau>)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (App \<F> t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
  then show ?case
    by (auto intro: has_type.intros)
next
  case (Abs \<F> t \<tau>\<^sub>1 \<tau>\<^sub>3 \<X>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Abs)
    fix y
    assume y_in: "y |\<notin>| finsert x (free_vars_fset t |\<union>| free_vars_fset u |\<union>| \<X>)"

    then have "x \<noteq> y"
      by blast

    moreover have "locally_closed u"
      using Abs.prems by auto

    moreover have "has_type \<C> (\<F>(y := \<tau>\<^sub>1)) (subst_free x u (subst_bound 0 (Free y) t)) \<tau>\<^sub>3"
    proof (rule Abs.IH)
      show "y |\<notin>| \<X>"
        using y_in by simp
    next
      show "(\<F>(y := \<tau>\<^sub>1)) x = \<tau>\<^sub>2"
        using Abs.prems \<open>x \<noteq> y\<close> by simp
    next
      have "y \<notin> free_vars u"
      by (metis y_in free_vars_fset.rep_eq[of u] funion_finsert_left[of x] funionCI[of y])

      then show "has_type \<C> (\<F>(y := \<tau>\<^sub>1)) u \<tau>\<^sub>2"
        using Abs.prems has_type_weaken_funenv by metis
    qed

    ultimately show "has_type \<C> (\<F>(y := \<tau>\<^sub>1)) (subst_bound 0 (Free y) (subst_free x u t)) \<tau>\<^sub>3"
      using subst_free_commutes_with_subst_bound_Free[OF inf_vars] by metis
  qed
qed


end