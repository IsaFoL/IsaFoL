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
    Neq_tconst :: 'a and
    Diff_tconst :: 'a

class type_signature = arity +
  fixes bool_tyctr :: 'a  and fun_tyctr :: 'a
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
  is_ground = "\<lambda>x. type_vars_prety x = {}" and
  apply_subst = "\<lambda>x \<sigma>. \<sigma> x" and
  (* subst_update = "\<lambda>\<sigma> x \<tau>. \<sigma>(x := \<tau>)" and *)
  vars = type_vars_prety
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
qed simp_all
(* next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety"
  assume "\<And>x. x \<in> type_vars_prety \<tau> \<Longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  then show "subst_prety \<tau> \<sigma>\<^sub>1 = subst_prety \<tau> \<sigma>\<^sub>2"
    by (induction \<tau>) auto
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and \<sigma> :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and x :: '\<V>\<^sub>t\<^sub>y
  show "(\<sigma>(x := \<tau>)) x = \<tau>"
    by simp
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and \<sigma> :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) prety" and x y :: '\<V>\<^sub>t\<^sub>y
  show "x \<noteq> y \<Longrightarrow> (\<sigma>(y := \<tau>)) x = \<sigma> x"
    by simp
qed *)

find_theorems "subst_prety"
                                                            
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
  "length \<tau>s = arity \<kappa> \<Longrightarrow> TyCtr \<kappa> \<tau>s = Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s))"

lemma PretyCtr_transfer[transfer_rule]:
  assumes "length \<tau>s = arity \<kappa>"
  assumes "list_all2 (pcr_ty (=) (=)) \<tau>s \<tau>s'"
  shows "pcr_ty (=) (=) (PretyCtr \<kappa> \<tau>s) (TyCtr \<kappa> \<tau>s')"
proof -
  have "TyCtr \<kappa> \<tau>s' = Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s'))"
    by (metis TyCtr_def assms(1,2) list_all2_lengthD)

  have "Rep_ty (Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s'))) = PretyCtr \<kappa> (map Rep_ty \<tau>s')"
  proof (rule Abs_ty_inverse)
    show "PretyCtr \<kappa> (map Rep_ty \<tau>s') \<in> {\<tau>. wf_prety \<tau>}"
      by (metis (no_types, opaque_lifting) PretyCtr Rep_ty assms(1,2) ex_map_conv length_map
          list_all2_lengthD mem_Collect_eq)
  qed

  have "map Rep_ty \<tau>s' = \<tau>s"
    using \<open>list_all2 (pcr_ty (=) (=)) \<tau>s \<tau>s'\<close>
    by (induction rule: list.rel_induct) (simp_all add: cr_ty_def ty.pcr_cr_eq)

  show ?thesis
    unfolding ty.pcr_cr_eq cr_ty_def
    unfolding \<open>TyCtr \<kappa> \<tau>s' = _\<close>
    unfolding \<open>Rep_ty (Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s'))) = _\<close>
    unfolding \<open>map Rep_ty \<tau>s' = _\<close> ..
qed

text \<open>@{thm PretyCtr_transfer} is an unsuccessful attempt to define a transfer rule for \<^const>\<open>TyCtr\<close>.\<close>

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
    then have "length (map Abs_ty \<tau>s) = arity \<kappa>"
      by simp

    have "P (TyCtr \<kappa> (map Abs_ty \<tau>s))"
    proof (rule TyCtr_case)
      show "length (map Abs_ty \<tau>s) = arity \<kappa>"
        using \<open>length (map Abs_ty \<tau>s) = arity \<kappa>\<close> .
    next
      show "\<And>\<tau>. \<tau> \<in> set (map Abs_ty \<tau>s) \<Longrightarrow> P \<tau>"
        using PretyCtr.IH by auto
    qed

    then have "P (Abs_ty (PretyCtr \<kappa> (map Rep_ty (map Abs_ty \<tau>s))))"
      unfolding TyCtr_def[OF \<open>length (map Abs_ty \<tau>s) = arity \<kappa>\<close>, symmetric] .

    moreover have "map Rep_ty (map Abs_ty \<tau>s) = \<tau>s"
      by (simp add: list.map_comp comp_def list.map_ident_strong Abs_ty_inverse PretyCtr.IH)

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

lemma "finite (type_vars \<tau>)"
  by (induction \<tau>) simp_all


subsection \<open>Common Types\<close>

lemma wf_prety_PretyCtr_bool_tyctr[intro]: "wf_prety (PretyCtr bool_tyctr [])"
  by (rule wf_prety.PretyCtr) simp_all

definition TyBool :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty" ("\<bool>") where
  "\<bool> \<equiv> Abs_ty (PretyCtr bool_tyctr [])"


lemma wf_prety_PretyCtr_fun_tyctr[intro]: "wf_prety (PretyCtr fun_tyctr [Rep_ty \<tau>\<^sub>1, Rep_ty \<tau>\<^sub>2])"
proof (intro wf_prety.PretyCtr[rule_format])
  show "\<And>x. x \<in> set [Rep_ty \<tau>\<^sub>1, Rep_ty \<tau>\<^sub>2] \<Longrightarrow> wf_prety x"
    using Rep_ty by auto
qed simp_all

abbreviation TyFun ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow>
    ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty" where
  "TyFun \<tau>\<^sub>1 \<tau>\<^sub>2 \<equiv> TyCtr fun_tyctr [\<tau>\<^sub>1, \<tau>\<^sub>2]"

abbreviation is_TyFun where
  "is_TyFun \<tau> \<equiv> \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau> = TyFun \<tau>\<^sub>1 \<tau>\<^sub>2"


subsection \<open>Size\<close>

lift_definition size_ty :: "('\<V>\<^sub>t\<^sub>y \<Rightarrow> nat) \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y \<Rightarrow> nat) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty \<Rightarrow> nat"
  is size_prety .

lemma size_ty_TyVar: "size_ty f\<^sub>1 f\<^sub>2 (TyVar x) = f\<^sub>1 x + Suc 0"
  by transfer simp


lemma size_ty_TyCtr:
  assumes "length \<tau>s = arity \<kappa>"
  shows "size_ty f\<^sub>1 f\<^sub>2 (TyCtr \<kappa> \<tau>s) = f\<^sub>2 \<kappa> + size_list (size_ty f\<^sub>1 f\<^sub>2) \<tau>s + Suc 0"
proof -
  have *: "Rep_ty (Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s))) = (PretyCtr \<kappa> (map Rep_ty \<tau>s))"
  proof (rule Abs_ty_inverse[simplified])
    show "wf_prety (PretyCtr \<kappa> (map Rep_ty \<tau>s))"
      by (simp add: assms wf_prety_PretyCtr)
  qed

  then show ?thesis
    unfolding TyCtr_def[OF \<open>length \<tau>s = arity \<kappa>\<close>]
    unfolding size_ty.rep_eq
    by (simp add: comp_def)
qed

lemma size_ty_TyFun:
  "size_ty f\<^sub>1 f\<^sub>2 (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) = f\<^sub>2 fun_tyctr + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>1  + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>2 + 3"
  using size_ty_TyCtr[of "[\<tau>\<^sub>1, \<tau>\<^sub>2]" fun_tyctr, simplified]
  by presburger


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
    by transfer simp
next
  assume assm: "length \<tau>s = arity \<kappa>"
  have "Abs_ty (PretyCtr \<kappa> (map (Rep_ty \<circ> (\<lambda>t. t \<cdot>\<^sub>t\<^sub>y \<sigma>)) \<tau>s)) = Abs_ty (Rep_ty (Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s)) \<cdot>\<^sub>t\<^sub>y \<sigma>))"
    by (simp add: Abs_ty_inverse assm subst_ty.rep_eq wf_prety_PretyCtr comp_def)
  also have "\<dots> = Abs_ty (PretyCtr \<kappa> (map Rep_ty \<tau>s)) \<cdot>\<^sub>t\<^sub>y \<sigma>"
    by (simp add: Rep_ty_inverse)
  finally show "TyCtr \<kappa> \<tau>s \<cdot>\<^sub>t\<^sub>y \<sigma> = TyCtr \<kappa> (map (\<lambda>\<tau>. \<tau> \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>s)"
    using assm by (simp add: TyCtr_def)
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

(*

  comp_subst = comp_subst_prety and
  id_subst = PretyVar and
  subst = subst_prety and
  apply_subst = "\<lambda>x \<sigma>. \<sigma> x" and
  subst_update = "\<lambda>\<sigma> x \<tau>. \<sigma>(x := \<tau>)" and
  vars = type_vars_prety
*)

global_interpretation subst_ty: substitution where
  comp_subst = comp_subst_ty and
  id_subst = TyVar and
  subst = subst_ty and
  is_ground = "\<lambda>x. type_vars x = {}" and
  apply_subst = "\<lambda>x \<sigma>. \<sigma> x" and
  (* subst_update = "\<lambda>\<sigma> x \<tau>. \<sigma>(x := \<tau>)" and *)
  vars = type_vars
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
qed simp_all
(*   fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"
  assume "\<And>x. x \<in> type_vars \<tau> \<Longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  then show "subst_ty \<tau> \<sigma>\<^sub>1 = subst_ty \<tau> \<sigma>\<^sub>2"
    by (induction \<tau>) auto
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" and \<sigma> :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty" and x :: '\<V>\<^sub>t\<^sub>y
  show "(\<sigma>(x := \<tau>)) x = \<tau>"
    by simp
next
  fix \<tau> :: "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: arity) ty" and \<sigma> :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty" and x y :: '\<V>\<^sub>t\<^sub>y
  show "x \<noteq> y \<Longrightarrow> (\<sigma>(y := \<tau>)) x = \<sigma> x"
    by simp
qed *)

section \<open>Type System\<close>

type_synonym ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) const_ty = "'\<V>\<^sub>t\<^sub>y dlist \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty list \<times> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty"

inductive has_type ::
  "('\<Sigma> \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) const_ty) \<Rightarrow>
    (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty \<Rightarrow> bool"
  for \<C> where
  Const: "has_type \<C> (Const c \<tau>\<^sub>1s ts) \<tau>"
    if "\<C> c = (\<alpha>s, \<tau>\<^sub>2s, \<tau>\<^sub>3)" and "Dlist.length \<alpha>s = length \<tau>\<^sub>1s" and
      "\<sigma> = fun_upds TyVar (list_of_dlist \<alpha>s) \<tau>\<^sub>1s" and
      "list_all2 (has_type \<C>) ts (map (\<lambda>\<tau>\<^sub>2. \<tau>\<^sub>2 \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>\<^sub>2s)" and
      "\<tau> = \<tau>\<^sub>3 \<cdot>\<^sub>t\<^sub>y \<sigma>"
    for c \<tau>\<^sub>1s ts \<tau> |
  Free: "has_type \<C> (Free x \<tau>) \<tau>"
    for x \<tau> |
  App: "has_type \<C> (App t\<^sub>1 t\<^sub>2) \<tau>\<^sub>2"
    if "has_type \<C> t\<^sub>1 (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)" and "has_type \<C> t\<^sub>2 \<tau>\<^sub>1"
    for t\<^sub>1 t\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 |
  Abs: "has_type \<C> (Abs \<tau>\<^sub>1 t) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    if "\<And>x. x |\<notin>| \<X> \<Longrightarrow> has_type \<C> (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t) \<tau>\<^sub>2"
    for t \<tau>\<^sub>1 \<tau>\<^sub>2 \<X>

lemma locally_closed_if_has_type[intro]: "has_type \<C> t \<tau> \<Longrightarrow> locally_closed t"
proof (induction t \<tau> rule: has_type.induct)
  case (Const c \<tau>\<^sub>1s ts \<tau> \<alpha>s \<tau>\<^sub>2s \<tau>\<^sub>3 \<sigma>)
  show ?case
  proof (rule locally_closed.Const)
    show "list_all locally_closed ts"
      using Const.IH
      by (simp add: list_all2_conv_all_nth list_all_length)
  qed
next
  case Free
  show ?case
    by (rule locally_closed.Free)
next
  case App
  then show ?case
    by (auto intro: locally_closed.App)
next
  case (Abs t \<tau>\<^sub>1 \<tau>\<^sub>2 \<X>)
  show ?case
  proof (rule locally_closed.Abs[where \<X> = \<X>])
    fix x
    assume "x |\<notin>| \<X>"
    then show "locally_closed (open_bound 0 \<tau>\<^sub>1 (Free x \<tau>\<^sub>1) t)"
      by (rule Abs.IH)
  qed
qed

text \<open>Since \<^const>\<open>has_type\<close> no longer carries a typing environment for free variables (they are
  typed by their own annotation instead), soundly substituting \<open>u\<close> for \<open>x\<close> in a well-typed term
  requires every occurrence of \<open>x\<close> in that term to carry the same annotation as \<open>u\<close>'s type ---
  \<^const>\<open>subst_free\<close> matches on the variable's name alone and ignores the stored annotation.
  \<open>free_var_types\<close> (defined below) collects those annotations.\<close>

primrec free_var_types :: "'\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> '\<tau> set" where
  "free_var_types x (Const c \<tau>s ts) = {}" |
  "free_var_types x (Free y \<tau>) = (if x = y then {\<tau>} else {})" |
  "free_var_types x (Bound k \<tau>) = {}" |
  "free_var_types x (App t\<^sub>1 t\<^sub>2) = free_var_types x t\<^sub>1 \<union> free_var_types x t\<^sub>2" |
  "free_var_types x (Abs \<tau> t) = free_var_types x t"

text \<open>\<^const>\<open>free_var_types\<close> ignores a \<open>Const\<close>'s parameters, matching the opacity of
  \<^const>\<open>subst_free\<close> and \<^const>\<open>open_bound\<close> towards them (see the note on
  \<^const>\<open>locally_closed_at\<close>): since substitution never descends into a constant's parameters,
  their annotations are irrelevant to the soundness of the substitution lemma below.\<close>

lemma free_var_types_empty_if_not_in_free_vars:
  "x \<notin> free_vars t \<Longrightarrow> free_var_types x t = {}"
  by (induction t) auto

lemma free_var_types_open_bound_Free_other[simp]:
  "x \<noteq> y \<Longrightarrow> free_var_types x (open_bound n \<tau> (Free y \<tau>) t) = free_var_types x t"
  by (induction t arbitrary: n) auto

lemma free_var_types_open_bound_Free_subset:
  "free_var_types x (open_bound n \<tau> (Free x \<tau>) t) \<subseteq> insert \<tau> (free_var_types x t)"
  by (induction t arbitrary: n) auto

lemma has_type_subst_free:
  fixes t :: "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes ht_t: "has_type \<C> t \<tau>\<^sub>1" and consistent: "free_var_types x t \<subseteq> {\<tau>\<^sub>2}"
    and ht_u: "has_type \<C> u \<tau>\<^sub>2"
  shows "has_type \<C> (subst_free x u t) \<tau>\<^sub>1"
  using ht_t consistent
proof (induction t \<tau>\<^sub>1 rule: has_type.induct)
  case (Const c \<tau>\<^sub>1s ts \<tau> \<alpha>s \<tau>\<^sub>2s \<tau>\<^sub>3 \<sigma>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Const)
    show "\<C> c = (\<alpha>s, \<tau>\<^sub>2s, \<tau>\<^sub>3)" by (rule Const.hyps(1))
    show "Dlist.length \<alpha>s = length \<tau>\<^sub>1s" by (rule Const.hyps(2))
    show "\<sigma> = fun_upds TyVar (list_of_dlist \<alpha>s) \<tau>\<^sub>1s" by (rule Const.hyps(3))
    show "list_all2 (has_type \<C>) ts (map (\<lambda>\<tau>\<^sub>2. \<tau>\<^sub>2 \<cdot>\<^sub>t\<^sub>y \<sigma>) \<tau>\<^sub>2s)"
      by (rule list.rel_mono_strong[OF Const.IH]) simp
    show "\<tau> = \<tau>\<^sub>3 \<cdot>\<^sub>t\<^sub>y \<sigma>" by (rule Const.hyps(4))
  qed
next
  case (Free y \<tau>)
  show ?case
  proof (cases "x = y")
    case True
    then have "\<tau> = \<tau>\<^sub>2"
      using Free.prems by auto
    then show ?thesis
      using True ht_u by (simp add: has_type.Free)
  next
    case False
    then show ?thesis
      by (simp add: has_type.Free)
  qed
next
  case (App s\<^sub>1 s\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2)
  have prems1: "free_var_types x s\<^sub>1 \<subseteq> {\<tau>\<^sub>2}" and prems2: "free_var_types x s\<^sub>2 \<subseteq> {\<tau>\<^sub>2}"
    using App.prems by auto
  have "has_type \<C> (subst_free x u s\<^sub>1) (TyFun \<rho>\<^sub>1 \<rho>\<^sub>2)"
    using App.IH(1)[OF prems1] .
  moreover have "has_type \<C> (subst_free x u s\<^sub>2) \<rho>\<^sub>1"
    using App.IH(2)[OF prems2] .
  ultimately show ?case
    unfolding subst_free.simps
    by (rule has_type.App)
next
  case (Abs t \<rho>\<^sub>1 \<rho>\<^sub>2 \<X>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Abs[where \<X> = "finsert x \<X>"])
    fix y
    assume y_in: "y |\<notin>| finsert x \<X>"
    then have x_ne_y: "x \<noteq> y" and y_notin_\<X>: "y |\<notin>| \<X>"
      by auto
    have consistent': "free_var_types x (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) t) \<subseteq> {\<tau>\<^sub>2}"
      using Abs.prems x_ne_y by simp
    have "has_type \<C> (subst_free x u (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) t)) \<rho>\<^sub>2"
      using Abs.IH[OF y_notin_\<X> consistent'] .
    then show "has_type \<C> (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) (subst_free x u t)) \<rho>\<^sub>2"
      using subst_free_commutes_with_open_bound_Free[
          OF inf_vars x_ne_y locally_closed_if_has_type[OF ht_u]]
      by metis
  qed
qed

lemma has_type_open_bound:
  fixes t :: "(('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes body_typed: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> has_type \<C> (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t) \<tau>\<^sub>1"
    and arg_typed: "has_type \<C> u \<tau>\<^sub>2"
  shows "has_type \<C> (open_bound 0 \<tau>\<^sub>2 u t) \<tau>\<^sub>1"
proof -
  obtain x where fresh_\<X>: "x |\<notin>| \<X>" and fresh_t: "x \<notin> free_vars t"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t|}"]
    by blast
  have consistent: "free_var_types x (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t) \<subseteq> {\<tau>\<^sub>2}"
    using free_var_types_open_bound_Free_subset[of x 0 \<tau>\<^sub>2 t]
    by (simp add: free_var_types_empty_if_not_in_free_vars[OF fresh_t])
  have "has_type \<C> (subst_free x u (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t)) \<tau>\<^sub>1"
    by (rule has_type_subst_free[OF inf_vars body_typed[OF fresh_\<X>] consistent arg_typed])
  then show ?thesis
    by (simp add: subst_free_open_bound_Free_eq_open_bound[OF fresh_t])
qed


end