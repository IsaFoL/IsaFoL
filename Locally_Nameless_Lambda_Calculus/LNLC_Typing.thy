theory LNLC_Typing
  imports
    LNLC_Term
    "Abstract_Substitution.Based_Substitution"
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


section \<open>Types\<close>

typedef (overloaded) ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<tau>) ty_comb (infixr "$" 65) =
  "{(s :: '\<Sigma>\<^sub>t\<^sub>y, Ts :: '\<tau> list). arity s = length Ts}"
  by (auto intro!: exI[of _ "replicate _ undefined"])

setup_lifting type_definition_ty_comb

lift_bnf (no_warn_wits) (dead 'c :: arity, 'ty) ty_comb
  by force+

lift_definition tycon :: "'\<Sigma>\<^sub>t\<^sub>y :: arity $ '\<tau> \<Rightarrow> '\<Sigma>\<^sub>t\<^sub>y" is fst .
lift_definition tyargs :: "'\<Sigma>\<^sub>t\<^sub>y :: arity $ '\<tau> \<Rightarrow> '\<tau> list" is snd .

lemma tycon_map_ty_comb[simp]: "tycon (map_ty_comb f x) = tycon x"
  by transfer simp

lemma tyargs_map_ty_comb[simp]: "tyargs (map_ty_comb f x) = map f (tyargs x)"
  by transfer simp

lemma set_tyargs[simp]: "set (tyargs fts) = set_ty_comb fts"
  by transfer auto

lemma length_tyargs[simp]: "length (tyargs t) = arity (tycon t)"
  by transfer auto

declare [[typedef_overloaded]]

datatype ('\<Sigma>\<^sub>t\<^sub>y :: arity, free_vars_ty: '\<V>\<^sub>t\<^sub>y) ty =
  TyVar '\<V>\<^sub>t\<^sub>y |
  TyCtr "'\<Sigma>\<^sub>t\<^sub>y $ ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty"

thm ty.size


subsection \<open>Substitutions\<close>

primrec subst_ty ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty) \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty" where
  "subst_ty \<sigma> (TyVar x) = \<sigma> x" |
  "subst_ty \<sigma> (TyCtr \<kappa>_\<tau>s) = TyCtr (map_ty_comb (subst_ty \<sigma>) \<kappa>_\<tau>s)"

abbreviation subst_ty_alt (infix "(\<cdot>\<^sub>t\<^sub>y)" 51) where
  "\<tau> \<cdot>\<^sub>t\<^sub>y \<sigma> \<equiv> subst_ty \<sigma> \<tau>"

lemma subst_prety_PretyVar[simp]: "subst_ty TyVar \<tau> = \<tau>"
proof (induction \<tau>)
  case (TyVar x)
  show ?case
    by simp
next
  case (TyCtr x)
  then show ?case
    by (simp add: ty_comb.map_ident_strong)
qed

lemma subst_ty_subst_ty_conv: "subst_ty \<sigma>\<^sub>2 (subst_ty \<sigma>\<^sub>1 t) = subst_ty (\<lambda>x. subst_ty \<sigma>\<^sub>2 (\<sigma>\<^sub>1 x)) t"
proof (induction t)
  case (TyVar x)
  show ?case
    by simp
next
  case (TyCtr x)
  then show ?case
    unfolding subst_ty.simps ty.inject
    unfolding ty_comb.map_comp comp_def
    by (meson ty_comb.map_cong)
qed

definition comp_subst_ty ::
  "('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty) \<Rightarrow> ('\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty) \<Rightarrow> '\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty" where
  "comp_subst_ty \<sigma>\<^sub>1 \<sigma>\<^sub>2 x \<equiv> subst_ty \<sigma>\<^sub>2 (\<sigma>\<^sub>1 x)"

global_interpretation comp_subst_ty: monoid comp_subst_ty TyVar
proof unfold_locales
  fix \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sigma>\<^sub>3 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty"
  show "comp_subst_ty (comp_subst_ty \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 = comp_subst_ty \<sigma>\<^sub>1 (comp_subst_ty \<sigma>\<^sub>2 \<sigma>\<^sub>3)"
  proof (intro ext)
    show "\<And>x. comp_subst_ty (comp_subst_ty \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<sigma>\<^sub>3 x = comp_subst_ty \<sigma>\<^sub>1 (comp_subst_ty \<sigma>\<^sub>2 \<sigma>\<^sub>3) x"
      unfolding comp_subst_ty_def
      by (metis subst_ty_subst_ty_conv)
  qed
next
  show "\<And>\<tau>. comp_subst_ty TyVar \<tau> = \<tau>"
    unfolding comp_subst_ty_def
    by simp
next
  show "\<And>\<tau>. comp_subst_ty \<tau> TyVar = \<tau>"
    unfolding comp_subst_ty_def
    by simp
qed

global_interpretation subst_prety: base_substitution where
  comp_subst = comp_subst_ty and
  id_subst = TyVar and
  subst = "\<lambda>\<tau> \<sigma>. subst_ty \<sigma> \<tau>" and
  is_ground = "\<lambda>x. free_vars_ty x = {}" and
  apply_subst = "\<lambda>x \<sigma>. \<sigma> x" and
  vars = free_vars_ty
proof unfold_locales
  fix \<tau> :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) ty"
    and \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: "'\<V>\<^sub>t\<^sub>y \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty"
    and x :: '\<V>\<^sub>t\<^sub>y
  show "subst_ty (comp_subst_ty \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<tau> = subst_ty \<sigma>\<^sub>2 (subst_ty \<sigma>\<^sub>1 \<tau>)"
  proof (induction \<tau>)
    case (TyVar x)
    then show ?case
      by (simp add: comp_subst_ty_def)
  next
    case (TyCtr \<kappa>_\<tau>s)
    then show ?case
      by (auto simp: subst_ty_subst_ty_conv ty_comb.map_comp intro: ty_comb.map_cong0)
  qed

  show "subst_ty TyVar \<tau> = \<tau>"
    by simp

  show "free_vars_ty \<tau> = {} \<Longrightarrow> \<forall>\<sigma>. subst_ty \<sigma> \<tau> = \<tau>"
    by (induction \<tau>) (simp_all add: ty_comb.map_ident_strong)

  show "free_vars_ty \<tau> = {} \<Longrightarrow> free_vars_ty \<tau> = {}" .

  show "\<exists>\<tau>. free_vars_ty \<tau> \<noteq> {} \<Longrightarrow> free_vars_ty (TyVar x) = {x}"
    by simp

  show "comp_subst_ty \<sigma>\<^sub>1 \<sigma>\<^sub>2 x = subst_ty \<sigma>\<^sub>2 (\<sigma>\<^sub>1 x)"
    unfolding comp_subst_ty_def ..

  show "free_vars_ty (subst_ty \<sigma>\<^sub>1 \<tau>) = \<Union> (free_vars_ty ` \<sigma>\<^sub>1 ` free_vars_ty \<tau>)"
    by (induction \<tau>) (simp_all add: ty_comb.set_map)

  show "free_vars_ty (subst_ty \<sigma>\<^sub>1 \<tau>) = {} \<Longrightarrow> \<forall>x\<in>free_vars_ty \<tau>. free_vars_ty (\<sigma>\<^sub>1 x) = {}"
    by (induction \<tau>) (simp_all add: ty_comb.set_map)
qed


subsection \<open>Common Types\<close>

definition TyBool :: "('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) ty" ("\<bool>") where
  "TyBool \<equiv> TyCtr (Abs_ty_comb (bool_tyctr, []))"

abbreviation TyFun :: "('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) ty" where
  "TyFun \<tau>\<^sub>1 \<tau>\<^sub>2 \<equiv> TyCtr (Abs_ty_comb (fun_tyctr, [\<tau>\<^sub>1, \<tau>\<^sub>2]))"

abbreviation is_TyFun where
  "is_TyFun \<tau> \<equiv> \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau> = TyFun \<tau>\<^sub>1 \<tau>\<^sub>2"


subsection \<open>Size\<close>

(* TODO: Make the proof nice and submit to Tobias for inclusion to List *)
(* OR BETTER: have the size plugin generate it automatically *)
lemma size_list_transfer[transfer_rule]:
  "(rel_fun (rel_fun A (=)) (rel_fun (list_all2 A) (=))) size_list size_list"
  unfolding rel_fun_def
  apply safe
  subgoal premises prems for f g xs ys
    using prems(2)
    apply (induct xs ys rule: list.rel_induct)
     apply (auto simp: prems(1))
    done
  done

(* lemma size_ty_TyCtr:
  shows "size_ty f\<^sub>1 f\<^sub>2 (TyCtr \<kappa>_\<tau>s) =
    f\<^sub>2 (tycon \<kappa>_\<tau>s) + size_list (size_ty f\<^sub>1 f\<^sub>2) (tyargs \<kappa>_\<tau>s) + Suc 0"
  using ty.size

lemma size_ty_TyFun:
  "size_ty f\<^sub>1 f\<^sub>2 (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) = f\<^sub>2 fun_tyctr + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>1  + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>2 + 3"
  using size_ty_TyCtr[of "[\<tau>\<^sub>1, \<tau>\<^sub>2]" fun_tyctr, simplified]
  by presburger *)


section \<open>Type System\<close>

type_synonym ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) pre_const_ty = "'\<V>\<^sub>t\<^sub>y list \<times> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty list \<times> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty"

text \<open>A constant's declared type-variable tuple must be distinct and must contain every type
  variable occurring in its parameter and result types, matching the paper's signature
  well-formedness requirement.\<close>

definition wf_const_ty :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) pre_const_ty \<Rightarrow> bool" where
  "wf_const_ty \<equiv> \<lambda>(\<alpha>s, \<tau>s, \<tau>).
    distinct \<alpha>s \<and> (\<Union>\<tau>'\<in>set \<tau>s. free_vars_ty \<tau>') \<union> free_vars_ty \<tau> \<subseteq> set \<alpha>s"

typedef (overloaded) ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) const_ty =
  \<open>{c :: ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) pre_const_ty. wf_const_ty c}\<close>
proof (rule exI)
  show \<open>([undefined], [], TyVar undefined) \<in> {c. wf_const_ty c}\<close>
    by (simp add: wf_const_ty_def)
qed

setup_lifting type_definition_const_ty

term ty.rel_ty

lift_definition const_ty_vars :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) const_ty \<Rightarrow> '\<V>\<^sub>t\<^sub>y list"
  is fst .
lift_definition const_ty_dom :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) const_ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty list"
  is "fst \<circ> snd" .
lift_definition const_ty_codom :: "('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) const_ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty"
  is "snd \<circ> snd" .

definition ConstTy ::
  "'\<V>\<^sub>t\<^sub>y list \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty list \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: arity, '\<V>\<^sub>t\<^sub>y) const_ty" where
  "wf_const_ty (\<alpha>s, \<tau>s, \<tau>) \<Longrightarrow> ConstTy \<alpha>s \<tau>s \<tau> = Abs_const_ty (\<alpha>s, \<tau>s, \<tau>)"

lemma Rep_const_ty_ConstTy[simp]:
  assumes "wf_const_ty (\<alpha>s, \<tau>s, \<tau>)"
  shows "Rep_const_ty (ConstTy \<alpha>s \<tau>s \<tau>) = (\<alpha>s, \<tau>s, \<tau>)"
  using assms by (simp add: ConstTy_def Abs_const_ty_inverse)

inductive has_type ::
  "('\<Sigma> \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) const_ty) \<Rightarrow>
    (('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<Sigma>\<^sub>t\<^sub>y, '\<V>\<^sub>t\<^sub>y) ty \<Rightarrow> bool"
  for \<C> where
  Const: "has_type \<C> (Const c \<tau>\<^sub>1s ts) \<tau>"
    if "length (const_ty_vars (\<C> c)) = length \<tau>\<^sub>1s" and
      "\<sigma> = fun_upds TyVar (const_ty_vars (\<C> c)) \<tau>\<^sub>1s" and
      "list_all2 (has_type \<C>) ts (map (subst_ty \<sigma>) (const_ty_dom (\<C> c)))" and
      "\<tau> = const_ty_codom (\<C> c) \<cdot>\<^sub>t\<^sub>y \<sigma>"
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
  case (Const c \<tau>\<^sub>1s ts \<tau> \<sigma>)
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
  proof (rule locally_closed.Abs)
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
  fixes t\<^sub>1 :: "(('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes ht_t: "has_type \<C> t\<^sub>1 \<tau>\<^sub>1" and consistent: "free_var_types x t\<^sub>1 \<subseteq> {\<tau>\<^sub>2}"
    and ht_u: "has_type \<C> t\<^sub>2 \<tau>\<^sub>2"
  shows "has_type \<C> (subst_free x t\<^sub>2 t\<^sub>1) \<tau>\<^sub>1"
  using ht_t consistent
proof (induction t\<^sub>1 \<tau>\<^sub>1 rule: has_type.induct)
  case (Const c \<tau>\<^sub>1s ts \<tau> \<sigma>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Const)
    show "length (const_ty_vars (\<C> c)) = length \<tau>\<^sub>1s"
      by (rule Const.hyps)
    show "\<sigma> = fun_upds TyVar (const_ty_vars (\<C> c)) \<tau>\<^sub>1s"
      by (rule Const.hyps)
    show "list_all2 (has_type \<C>) ts (map (\<lambda>\<tau>\<^sub>2. \<tau>\<^sub>2 \<cdot>\<^sub>t\<^sub>y \<sigma>) (const_ty_dom (\<C> c)))"
      by (rule list.rel_mono_strong[OF Const.IH]) simp
    show "\<tau> = const_ty_codom (\<C> c) \<cdot>\<^sub>t\<^sub>y \<sigma>"
      by (rule Const.hyps)
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
  have "has_type \<C> (subst_free x t\<^sub>2 s\<^sub>1) (TyFun \<rho>\<^sub>1 \<rho>\<^sub>2)"
    using App.IH(1)[OF prems1] .
  moreover have "has_type \<C> (subst_free x t\<^sub>2 s\<^sub>2) \<rho>\<^sub>1"
    using App.IH(2)[OF prems2] .
  ultimately show ?case
    unfolding subst_free.simps
    by (rule has_type.App)
next
  case (Abs t \<rho>\<^sub>1 \<rho>\<^sub>2 \<X>)
  show ?case
    unfolding subst_free.simps
  proof (rule has_type.Abs)
    fix y :: '\<V>
    assume y_in: "y |\<notin>| finsert x \<X>"
    then have x_ne_y: "x \<noteq> y" and y_notin_\<X>: "y |\<notin>| \<X>"
      by auto
    have consistent': "free_var_types x (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) t) \<subseteq> {\<tau>\<^sub>2}"
      using Abs.prems x_ne_y by simp
    have "has_type \<C> (subst_free x t\<^sub>2 (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) t)) \<rho>\<^sub>2"
      using Abs.IH[OF y_notin_\<X> consistent'] .
    then show "has_type \<C> (open_bound 0 \<rho>\<^sub>1 (Free y \<rho>\<^sub>1) (subst_free x t\<^sub>2 t)) \<rho>\<^sub>2"
      unfolding subst_free_commutes_with_open_bound_Free[
          OF inf_vars x_ne_y locally_closed_if_has_type[OF ht_u]] .
  qed
qed

lemma has_type_open_bound:
  fixes t\<^sub>1 :: "(('\<Sigma>\<^sub>t\<^sub>y :: type_signature, '\<V>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes body_typed: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> has_type \<C> (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t\<^sub>1) \<tau>\<^sub>1"
    and arg_typed: "has_type \<C> t\<^sub>2 \<tau>\<^sub>2"
  shows "has_type \<C> (open_bound 0 \<tau>\<^sub>2 t\<^sub>2 t\<^sub>1) \<tau>\<^sub>1"
proof -
  obtain x :: '\<V> where fresh_\<X>: "x |\<notin>| \<X>" and fresh_t: "x \<notin> free_vars t\<^sub>1"
    using fresh_for_fset_and_terms[OF inf_vars, where \<X> = \<X> and \<T> = "{|t\<^sub>1|}"]
    by auto
  have consistent: "free_var_types x (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t\<^sub>1) \<subseteq> {\<tau>\<^sub>2}"
    using free_var_types_open_bound_Free_subset[of x 0 \<tau>\<^sub>2 t\<^sub>1]
    by (simp add: free_var_types_empty_if_not_in_free_vars[OF fresh_t])
  have "has_type \<C> (subst_free x t\<^sub>2 (open_bound 0 \<tau>\<^sub>2 (Free x \<tau>\<^sub>2) t\<^sub>1)) \<tau>\<^sub>1"
    by (rule has_type_subst_free[OF inf_vars body_typed[OF fresh_\<X>] consistent arg_typed])
  then show ?thesis
    by (simp add: subst_free_open_bound_Free_eq_open_bound[OF fresh_t])
qed

end