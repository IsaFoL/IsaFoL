theory LN_Lambda_Strong_Normalization
  imports
    LN_Lambda_Reduction
    LN_Lambda_Typing
begin

text \<open>Strong normalization of the well-typed fragment, via Tait/Girard reducibility.

  \<^bold>\<open>Status:\<close> this file currently contains only the definitions and the statements of every
  lemma; all proofs are \<^theory_text>\<open>sorry\<close>, awaiting review before they are discharged.\<close>


section \<open>Strong normalization predicate\<close>

text \<open>\<open>SN t\<close> holds when every \<open>\<beta>\<close>-reduction sequence starting from \<open>t\<close> terminates. Rather than a
  bespoke predicate we reuse the accessible part \<^const>\<open>Wellfounded.accp\<close> of one-step reduction;
  \<open>SN\<close> is merely an abbreviation (no new constant), so all of \<^const>\<open>Wellfounded.accp\<close>'s library
  (well-founded induction, etc.) is available directly.\<close>

abbreviation SN :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "SN \<equiv> Wellfounded.accp beta_reduce\<inverse>\<inverse>"

lemma SN_step: "SN t \<Longrightarrow> beta_reduce t u \<Longrightarrow> SN u"
  by (meson accp.cases conversep_iff)

lemma SN_AppD: "SN (App t u) \<Longrightarrow> SN t \<and> SN u"
proof (induction "App t u" arbitrary: t u rule: accp_induct_rule)
  case 1
  then show ?case
    unfolding conversep_iff
    by (metis App_left App_right accpI)
qed

lemma SN_AbsD: "SN (Abs \<tau> t) \<Longrightarrow> SN t"
proof (induction "Abs \<tau> t" arbitrary: \<tau> t rule: accp_induct_rule)
  case 1
  then show ?case
    by (metis beta_reduce.Abs conversep_iff not_accp_down)
qed

lemma SN_ConstD: "SN (Const c \<tau>s ts) \<Longrightarrow> t \<in> set ts \<Longrightarrow> SN t"
proof (induction "Const c \<tau>s ts" arbitrary: c \<tau>s ts t rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule accpI)
    fix t'
    assume "beta_reduce\<inverse>\<inverse> t' t"
    then have "beta_reduce t t'"
      by simp
    obtain i where "i < length ts" and "ts ! i = t"
      using "1.prems" by (meson in_set_conv_nth)
    then have "beta_reduce (Const c \<tau>s ts) (Const c \<tau>s (ts[i := t']))"
      using \<open>beta_reduce t t'\<close> by (metis beta_reduce.Const)
    moreover have "t' \<in> set (ts[i := t'])"
      using \<open>i < length ts\<close> by (simp add: set_update_memI)
    ultimately show "SN t'"
      using IH by (metis conversep_iff)
  qed
qed

lemma SN_subst_bound_FreeD: "SN (subst_bound 0 (Free x) t) \<Longrightarrow> SN t"
  sorry

text \<open>Bridge to the goal: if every element of a set is strongly normalizing, then the reversed
  reduction relation is well-founded on that set.\<close>

lemma wfp_on_beta_reduce_if_SN:
  assumes "\<And>t. t \<in> A \<Longrightarrow> SN t"
  shows "wfp_on A beta_reduce\<inverse>\<inverse>"
proof -
  have "Wellfounded.accp (\<lambda>x y. beta_reduce y x \<and> x \<in> A \<and> y \<in> A) y"
    if "beta_reduce x y" and "y \<in> A" and "x \<in> A"
    for x y
    using assms(1)[OF \<open>y \<in> A\<close>, unfolded conversep_iff] that
    by (smt (verit, ccfv_SIG) accpI accp_induct)

  then show ?thesis
  unfolding conversep_iff
  unfolding wfp_on_iff_wfp[of A]
  by (metis (no_types, lifting) accpI accp_wfpI)
qed


section \<open>Reducibility candidates\<close>

text \<open>A term is \<^emph>\<open>neutral\<close> when it is not an abstraction; applying it to an argument creates no
  redex at the root.\<close>

definition neutral :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "neutral t \<longleftrightarrow> \<not> is_Abs t"

text \<open>Reducibility \<open>Red \<tau> t\<close> is defined by recursion on the type \<open>\<tau>\<close>. We recurse on the underlying
  \<^type>\<open>prety\<close> and lift the result to \<^type>\<open>ty\<close>. At a function type a term is reducible iff it is
  strongly normalizing and sends reducible, locally closed arguments to reducible results; at any
  other type reducibility is just strong normalization.\<close>

fun Red_prety ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) prety \<Rightarrow>
    (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "Red_prety (PretyCtr \<kappa> [\<tau>\<^sub>1, \<tau>\<^sub>2]) t =
    (if \<kappa> = fun_tyctr then
       SN t \<and> (\<forall>u. locally_closed u \<longrightarrow> Red_prety \<tau>\<^sub>1 u \<longrightarrow> Red_prety \<tau>\<^sub>2 (App t u))
     else SN t)" |
  "Red_prety _ t = SN t"

definition Red ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "Red \<tau> t \<longleftrightarrow> Red_prety (Rep_ty \<tau>) t"


lemma Red_TyFun:
  "Red (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) t \<longleftrightarrow>
     SN t \<and> (\<forall>u. locally_closed u \<longrightarrow> Red \<tau>\<^sub>1 u \<longrightarrow> Red \<tau>\<^sub>2 (App t u))"
  unfolding Red_def TyCtr_def
  by (simp add: Abs_ty_inverse wf_prety_PretyCtr_fun_tyctr)

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
  unfolding TyCtr_def
  unfolding size_ty.rep_eq
  by (simp add: comp_def)
qed

lemma size_ty_TyFun: "size_ty f\<^sub>1 f\<^sub>2 (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) = f\<^sub>2 fun_tyctr + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>1  + size_ty f\<^sub>1 f\<^sub>2 \<tau>\<^sub>2 + 3"
  using size_ty_TyCtr[of "[\<tau>\<^sub>1, \<tau>\<^sub>2]" fun_tyctr, simplified]
  by presburger

function Red_ty ::
  "('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y :: type_signature) ty \<Rightarrow> (('\<V>\<^sub>t\<^sub>y, '\<Sigma>\<^sub>t\<^sub>y) ty, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) t \<longleftrightarrow> (SN t \<and> (\<forall>u. locally_closed u \<longrightarrow> Red_ty \<tau>\<^sub>1 u \<longrightarrow> Red_ty \<tau>\<^sub>2 (App t u)))" |
  "\<not> is_TyFun \<tau> \<Longrightarrow> Red_ty \<tau> t \<longleftrightarrow> SN t"
proof -
  \<comment> \<open>Pattern completeness\<close>
  show "\<And>P x. (\<And>\<tau>\<^sub>1 \<tau>\<^sub>2 t. x = (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<Longrightarrow> P) \<Longrightarrow> (\<And>\<tau> t. \<not> is_TyFun \<tau> \<Longrightarrow> x = (\<tau>, t) \<Longrightarrow> P) \<Longrightarrow> P"
    by (metis prod.exhaust)

  \<comment> \<open>The remaining subgoals are pattern compatibility.\<close>
qed auto
termination
proof (relation "measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)")
  show "wf (measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>))"
    by simp
next
  fix \<tau>\<^sub>1 \<tau>\<^sub>2 t x
  assume "locally_closed x"
  then have "size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>\<^sub>1 < size_ty (\<lambda>_. 0) (\<lambda>_. 0) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    unfolding size_ty_TyFun
    by linarith
  then show "((\<tau>\<^sub>1, x), TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<in> measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)"
    by simp
next
  fix \<tau>\<^sub>1 \<tau>\<^sub>2 t x
  assume "locally_closed x" and "Red_ty \<tau>\<^sub>1 x" and "Red_ty_dom (\<tau>\<^sub>1, x)"
  then have "size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>\<^sub>2 < size_ty (\<lambda>_. 0) (\<lambda>_. 0) (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2)"
    unfolding size_ty_TyFun
    by linarith
  then show "((\<tau>\<^sub>2, App t x), TyFun \<tau>\<^sub>1 \<tau>\<^sub>2, t) \<in> measure (\<lambda>(\<tau>, t). size_ty (\<lambda>_. 0) (\<lambda>_. 0) \<tau>)"
    by simp
qed

lemma "Red = Red_ty"
proof (intro ext)
  fix \<tau> t
  show "Red \<tau> t = Red_ty \<tau> t"
  proof (induction \<tau> t rule: Red_ty.induct)
    case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
    then show ?case
      by (simp add: Red_TyFun)
  next
    case (2 \<tau> t)
    then show ?case
    proof (induction \<tau>)
      case (TyVar x)
      then show ?case
        by (simp add: Red_def TyVar_def Abs_ty_inverse wf_prety.PretyVar)
    next
      case (TyCtr \<kappa> \<tau>s)
      have "\<kappa> \<noteq> fun_tyctr"
        using TyCtr.prems TyCtr.hyps
        by (metis (no_types, lifting) arity\<^sub>_tyctr_simps(2) length_0_conv length_Suc_conv numerals(2))

      then have "Red (TyCtr \<kappa> \<tau>s) t = SN t"
        using wf_prety_PretyCtr[OF \<open>length \<tau>s = arity \<kappa>\<close>]
        by (cases "(PretyCtr \<kappa> (map Rep_ty \<tau>s), t)" rule: Red_prety.cases)
          (simp_all add: Red_def TyCtr_def Abs_ty_inverse[simplified])
      also have "SN t = Red_ty (TyCtr \<kappa> \<tau>s) t"
        using TyCtr.prems by simp
      finally show ?case .
    qed
  qed
qed

section \<open>Reducibility candidate properties (CR1--CR3)\<close>

lemma CR1: "Red \<tau> t \<Longrightarrow> SN t"
proof -
  assume a1: "Red \<tau> t"
  have "\<forall>t. All ((\<lambda>p. SN p \<or> \<not> Red t p)::(('a, 'b) ty, 'c, 'd) preterm \<Rightarrow> _)"
    by (smt (verit) Red_def Red_prety.elims(2))
  then show ?thesis
    using a1 by blast
qed

lemma CR2:
  assumes "Red \<tau> t" and "beta_reduce t t'"
  shows "Red \<tau> t'"
proof -
  have "Red_prety p a \<Longrightarrow> beta_reduce a b \<Longrightarrow> Red_prety p b" for p a b
  proof (induction p a arbitrary: b rule: Red_prety.induct)
    case (1 \<kappa> \<tau>\<^sub>1 \<tau>\<^sub>2 a)
    show ?case
    proof (cases "\<kappa> = fun_tyctr")
      case True
      have "SN a"
        using "1.prems"(1) True by simp
      then have "SN b"
        using "1.prems"(2) SN_step by blast
      moreover have "Red_prety \<tau>\<^sub>2 (App b u)"
        if u: "locally_closed u" "Red_prety \<tau>\<^sub>1 u" for u
      proof -
        have "Red_prety \<tau>\<^sub>2 (App a u)"
          using "1.prems"(1) True u by simp
        moreover have "beta_reduce (App a u) (App b u)"
          using "1.prems"(2) by (rule beta_reduce.App_left)
        ultimately show ?thesis
          using "1.IH"(2)[OF True u(1) u(2)] by blast
      qed
      ultimately show ?thesis
        using True by simp
    next
      case False
      have "SN a"
        using "1.prems"(1) False by simp
      then have "SN b"
        using "1.prems"(2) SN_step by blast
      then show ?thesis
        using False by simp
    qed
  qed (auto intro: SN_step)
  then show ?thesis
    using assms unfolding Red_def by blast
qed

lemma CR3:
  "neutral t \<Longrightarrow> locally_closed t \<Longrightarrow> (\<And>t'. beta_reduce t t' \<Longrightarrow> Red \<tau> t') \<Longrightarrow> Red \<tau> t"
  sorry

text \<open>In particular, free variables are reducible at every type (they are neutral and normal).\<close>

lemma Red_Free: "Red \<tau> (Free x)"
  sorry


section \<open>Reducibility of abstractions and constants\<close>

lemma Red_Abs:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed (Abs \<tau>\<^sub>1 t)"
  assumes "\<And>u. locally_closed u \<Longrightarrow> Red \<tau>\<^sub>1 u \<Longrightarrow> Red \<tau>\<^sub>2 (subst_bound 0 u t)"
  shows "Red (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) (Abs \<tau>\<^sub>1 t)"
  sorry

lemma Red_Const:
  assumes "locally_closed (Const c \<tau>s ts)"
  assumes "\<forall>t \<in> set ts. SN t"
  shows "Red \<tau> (Const c \<tau>s ts)"
  sorry


section \<open>Parallel substitution of free variables\<close>

text \<open>Simultaneous substitution of the free (named) variables. Contrary to \<^const>\<open>subst_bound\<close>,
  this descends into the parameters of a constant, which may contain free variables.\<close>

fun msubst ::
  "('\<V> \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm) \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm" where
  "msubst \<theta> (Const c \<tau>s ts) = Const c \<tau>s (map (msubst \<theta>) ts)" |
  "msubst \<theta> (Free x) = \<theta> x" |
  "msubst \<theta> (Bound n) = Bound n" |
  "msubst \<theta> (App t\<^sub>1 t\<^sub>2) = App (msubst \<theta> t\<^sub>1) (msubst \<theta> t\<^sub>2)" |
  "msubst \<theta> (Abs \<tau> t) = Abs \<tau> (msubst \<theta> t)"

lemma msubst_Free: "msubst Free t = t"
  by (induction t) (simp_all add: map_idI)

lemma msubst_cong:
  "(\<And>z. z \<in> free_vars t \<Longrightarrow> \<theta> z = \<theta>' z) \<Longrightarrow> msubst \<theta> t = msubst \<theta>' t"
  by (induction t) (auto cong: map_cong)

lemma locally_closed_msubst:
  "(\<And>y. locally_closed (\<theta> y)) \<Longrightarrow> locally_closed t \<Longrightarrow> locally_closed (msubst \<theta> t)"
  sorry

text \<open>Opening a fresh variable and then substituting it equals substituting into the opened body
  (the key commutation lemma for the abstraction case of the fundamental theorem).\<close>

lemma msubst_subst_bound_Free:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "x \<notin> free_vars t"
  assumes "\<And>y. locally_closed (\<theta> y)"
  shows "msubst (\<theta>(x := u)) (subst_bound n (Free x) t) = subst_bound n u (msubst \<theta> t)"
  sorry


section \<open>Fundamental theorem and strong normalization\<close>

text \<open>Every well-typed term is reducible under any reducible, locally closed substitution of its
  free variables.\<close>

lemma fundamental:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "has_type \<C> \<F> t \<tau>"
  assumes "\<And>x. locally_closed (\<theta> x)"
  assumes "\<And>x. Red (\<F> x) (\<theta> x)"
  shows "Red \<tau> (msubst \<theta> t)"
  sorry

lemma SN_if_has_type:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes ht: "has_type \<C> \<F> t \<tau>"
  shows "SN t"
proof -
  have "Red \<tau> (msubst Free t)"
  proof (rule fundamental[OF inf_vars ht])
    show "\<And>x. locally_closed (Free x)"
      by (rule locally_closed.Free)
  next
    show "\<And>x. Red (\<F> x) (Free x)"
      by (rule Red_Free)
  qed
  then show "SN t"
    by (metis CR1 msubst_Free)
qed

proposition strong_normalization_of_typed_terms:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "wfp_on {t. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>} beta_reduce\<inverse>\<inverse>"
  by (rule wfp_on_beta_reduce_if_SN) (auto intro: SN_if_has_type[OF inf_vars])

end
