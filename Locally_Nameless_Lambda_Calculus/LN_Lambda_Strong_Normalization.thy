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
    sorry
qed

lemma SN_AbsD: "SN (Abs \<tau> t) \<Longrightarrow> SN t"
proof (induction "Abs \<tau> t" arbitrary: \<tau> t rule: accp_induct_rule)
  case 1
  then show ?case
    sorry
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
proof (induction "subst_bound 0 (Free x) t" arbitrary: x t rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule accpI)
    fix t'
    assume "beta_reduce\<inverse>\<inverse> t' t"
    then have "beta_reduce t t'"
      by simp
    show "SN t'"
      apply (rule IH[where x = x])
      unfolding conversep_iff
      using \<open>beta_reduce t t'\<close>
    proof (induction rule: beta_reduce.induct)
      case (beta \<tau> t u)
      then show ?case
        apply simp
        sorry
    next
      case (App_left t t' u)
      then show ?case sorry
    next
      case (App_right u u' t)
      then show ?case sorry
    next
      case (Abs t t' \<tau>)
      then show ?case sorry
    next
      case (Const i ts t' c \<tau>s)
      then show ?case sorry
    qed
  qed
qed

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

text \<open>Reducibility \<open>Red_ty \<tau> t\<close> is defined by recursion on the type \<open>\<tau>\<close>. At a function type a term
  is reducible iff it is strongly normalizing and sends reducible, locally closed arguments to
  reducible results; at any other type reducibility is just strong normalization.\<close>

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

section \<open>Reducibility candidate properties (CR1--CR3)\<close>

lemma CR1: "Red_ty \<tau> t \<Longrightarrow> SN t"
  by (cases "is_TyFun \<tau>") auto

lemma CR2:
  assumes "Red_ty \<tau> t" and "beta_reduce t t'"
  shows "Red_ty \<tau> t'"
  using assms
proof (induction \<tau> t arbitrary: t' rule: Red_ty.induct)
  case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
  have "SN t'"
    using "1.prems" SN_step by (metis Red_ty.simps(1))
  moreover have "Red_ty \<tau>\<^sub>2 (App t' u)"
    if u: "locally_closed u" "Red_ty \<tau>\<^sub>1 u" for u
  proof -
    have "Red_ty \<tau>\<^sub>2 (App t u)"
      using "1.prems"(1) u by simp
    moreover have "beta_reduce (App t u) (App t' u)"
      using "1.prems"(2)
      by (metis App_left u(1))
    ultimately show ?thesis
      using "1.IH"(2)[OF u(1) u(2)] by blast
  qed
  ultimately show ?case
    by simp
next
  case (2 \<tau> t)
  then show ?case
    using SN_step by (metis Red_ty.simps(2))
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of an application with a \<^emph>\<open>neutral\<close> head: since the head is not an
  abstraction, no redex is created at the root, so the step happens in one of the two immediate
  subterms.\<close>

lemma beta_reduce_App_neutralD:
  assumes "beta_reduce (App t u) v" and "neutral t"
  shows "(\<exists>t'. v = App t' u \<and> beta_reduce t t') \<or> (\<exists>u'. v = App t u' \<and> beta_reduce u u')"
  using assms by (auto simp: neutral_def elim: beta_reduce.cases)

lemma CR3:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "neutral t" and "locally_closed t" and "\<And>t'. beta_reduce t t' \<Longrightarrow> Red_ty \<tau> t'"
  shows "Red_ty \<tau> t"
  using assms(2-)
proof (induction \<tau> t rule: Red_ty.induct)
  case (1 \<tau>\<^sub>1 \<tau>\<^sub>2 t)
  note neutral_t = "1.prems"(1) and lc_t = "1.prems"(2) and reds_t = "1.prems"(3)
  note IH2 = "1.IH"(2)
  have SN_t: "SN t"
  proof (rule accpI)
    fix y assume "beta_reduce\<inverse>\<inverse> y t"
    then have "beta_reduce t y" by simp
    then have "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) y" by (rule reds_t)
    then show "SN y" by (rule CR1)
  qed
  have red_App: "Red_ty \<tau>\<^sub>2 (App t u)" if "locally_closed u" and "Red_ty \<tau>\<^sub>1 u" for u
  proof -
    have "SN u" using \<open>Red_ty \<tau>\<^sub>1 u\<close> by (rule CR1)
    then show ?thesis using \<open>locally_closed u\<close> \<open>Red_ty \<tau>\<^sub>1 u\<close>
    proof (induction u rule: accp_induct_rule)
      case (1 w)
      note IH_w = "1.IH"
      note lc_w = "1.prems"(1) and red_w = "1.prems"(2)
      show ?case
      proof (rule IH2[OF lc_w red_w])
        show "neutral (App t w)"
          by (simp add: neutral_def)
      next
        show "locally_closed (App t w)"
          using lc_t lc_w by (rule locally_closed.App)
      next
        fix v assume "beta_reduce (App t w) v"
        from beta_reduce_App_neutralD[OF this neutral_t] show "Red_ty \<tau>\<^sub>2 v"
        proof
          assume "\<exists>t'. v = App t' w \<and> beta_reduce t t'"
          then obtain t' where v: "v = App t' w" and "beta_reduce t t'"
            by blast
          have "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) t'"
            by (rule reds_t[OF \<open>beta_reduce t t'\<close>])
          then have "Red_ty \<tau>\<^sub>2 (App t' w)"
            using lc_w red_w by simp
          then show "Red_ty \<tau>\<^sub>2 v"
            by (simp add: v)
        next
          assume "\<exists>u'. v = App t u' \<and> beta_reduce w u'"
          then obtain w' where v: "v = App t w'" and "beta_reduce w w'"
            by blast
          have "locally_closed w'"
            by (rule locally_closed_if_beta_reduce[OF inf_vars \<open>beta_reduce w w'\<close>])
          moreover have "Red_ty \<tau>\<^sub>1 w'"
            by (rule CR2[OF red_w \<open>beta_reduce w w'\<close>])
          moreover have "beta_reduce\<inverse>\<inverse> w' w"
            using \<open>beta_reduce w w'\<close> by (rule conversepI)
          ultimately have "Red_ty \<tau>\<^sub>2 (App t w')"
            using IH_w by blast
          then show "Red_ty \<tau>\<^sub>2 v"
            by (simp add: v)
        qed
      qed
    qed
  qed
  show ?case
    using SN_t red_App by auto
next
  case (2 \<tau> t)
  have "SN t"
  proof (rule accpI)
    fix y assume "beta_reduce\<inverse>\<inverse> y t"
    then have "beta_reduce t y" by simp
    then have "Red_ty \<tau> y" by (rule "2.prems"(3))
    then show "SN y" by (rule CR1)
  qed
  then show ?case
    using "2.hyps" by simp
qed

text \<open>In particular, free variables are reducible at every type (they are neutral and normal).\<close>

lemma SN_Free: "SN (Free x)"
proof (rule accpI)
  fix u
  assume "beta_reduce\<inverse>\<inverse> u (Free x)"
  then have False
    unfolding conversep_iff
    using beta_reduce.cases by fastforce
  then show "SN u" ..
qed

text \<open>A free variable is neutral, locally closed, and normal (no \<open>\<beta>\<close>-reduct), so \<open>CR3\<close>
  applies with a vacuous reduct hypothesis.\<close>

lemma Red_Free:
  fixes x :: '\<V>
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "Red_ty \<tau> (Free x)"
proof (rule CR3[OF inf_vars])
  show "neutral (Free x)"
    by (simp add: neutral_def)
next
  show "locally_closed (Free x)"
    by (rule locally_closed.Free)
next
  show "\<And>t'. beta_reduce (Free x) t' \<Longrightarrow> Red_ty \<tau> t'"
    by (auto elim: beta_reduce.cases)
qed


section \<open>Reducibility of abstractions and constants\<close>

text \<open>Strong normalization is inherited by an abstraction from its body.\<close>

lemma SN_Abs: "SN t \<Longrightarrow> SN (Abs \<tau> t)"
proof (induction t rule: accp_induct_rule)
  case (1 t)
  show ?case
  proof (rule accpI)
    fix v assume "beta_reduce\<inverse>\<inverse> v (Abs \<tau> t)"
    then have "beta_reduce (Abs \<tau> t) v"
      by simp
    then obtain t' \<X> where
      "v = Abs \<tau> t'" and
      br_sb_sb: "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
      by (auto elim!: beta_reduce.cases)
    then show "SN v"
      using "1.IH"
      by (metis conversepI)
  qed
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of a redex \<open>(\<lambda>. t) u\<close>: either the redex is contracted, or the step is
  taken inside the body or the argument.\<close>

lemma beta_reduce_AppD:
  assumes "beta_reduce (App a b) v"
  obtains (redex) \<tau> s where "a = Abs \<tau> s" and "v = subst_bound 0 b s"
    | (left) a' where "v = App a' b" and "beta_reduce a a'"
    | (right) b' where "v = App a b'" and "beta_reduce b b'"
  using assms by (auto elim: beta_reduce.cases)

lemma beta_reduce_App_AbsD:
  assumes "beta_reduce (App (Abs \<tau>\<^sub>1 t) u) v"
  shows "v = subst_bound 0 u t
    \<or> (\<exists>t'. v = App (Abs \<tau>\<^sub>1 t') u \<and> (\<exists>\<X>. \<forall>x. x |\<notin>| \<X> \<longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')))
    \<or> (\<exists>u'. v = App (Abs \<tau>\<^sub>1 t) u' \<and> beta_reduce u u')"
  using assms
proof (cases rule: beta_reduce_AppD)
  case (redex \<tau> s)
  then show ?thesis by auto
next
  case (left a')
  from \<open>beta_reduce (Abs \<tau>\<^sub>1 t) a'\<close> obtain \<X> t'
    where "a' = Abs \<tau>\<^sub>1 t'" and
      "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
    by (auto elim!: beta_reduce.cases)
  then show ?thesis
    using \<open>v = App a' u\<close>
    by blast
next
  case (right b')
  then show ?thesis by blast
qed

text \<open>Core of the abstraction lemma: \<open>(\<lambda>. t) u\<close> is reducible whenever \<open>t\<close> and \<open>u\<close> are strongly
  normalizing, \<open>u\<close> is reducible, and every reducible instance of the body is reducible. Since the
  redex is neutral (an application), we invoke \<open>CR3\<close> and discharge its reducts by a nested
  induction on \<open>SN t\<close> (for reductions in the body) and \<open>SN u\<close> (for reductions in the argument).\<close>

lemma Red_Abs_aux:
  fixes t u :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "SN t" and "SN u"
    and "body t" and "locally_closed u" and "Red_ty \<tau>\<^sub>1 u"
    and "\<And>v. locally_closed v \<Longrightarrow> Red_ty \<tau>\<^sub>1 v \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
  shows "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u)"
  using assms(2-)
proof (induction t arbitrary: u rule: accp_induct_rule)
  case (1 t)
  note outer_IH = "1.IH"
  note body_t = "1.prems"(2) and hyp_t = "1.prems"(5)
  from "1.prems"(1) show ?case
    using "1.prems"(3,4)
  proof (induction u rule: accp_induct_rule)
    case (1 u)
    note inner_IH = "1.IH"
    note lc_u = "1.prems"(1) and red_u = "1.prems"(2)
    show ?case
    proof (rule CR3[OF inf_vars])
      show "neutral (App (Abs \<tau>\<^sub>1 t) u)"
        by (simp add: neutral_def)
    next
      show "locally_closed (App (Abs \<tau>\<^sub>1 t) u)"
        using body_t lc_u
        by (simp add: locally_closed_App_iff locall_closed_Abs_iff_body)
    next
      fix w assume "beta_reduce (App (Abs \<tau>\<^sub>1 t) u) w"
      from beta_reduce_App_AbsD[OF this]
      consider (contract) "w = subst_bound 0 u t"
        | (body) t' \<X> where
            "w = App (Abs \<tau>\<^sub>1 t') u" and
            "\<And>x. x |\<notin>| \<X> \<Longrightarrow> beta_reduce (subst_bound 0 (Free x) t) (subst_bound 0 (Free x) t')"
        | (arg) u' where "w = App (Abs \<tau>\<^sub>1 t) u'" and "beta_reduce u u'"
        by blast
      then show "Red_ty \<tau>\<^sub>2 w"
      proof cases
        case contract
        then show ?thesis
          using hyp_t[OF lc_u red_u] by simp
      next
        case (body t')
        have SN_u: "SN u"
          using red_u by (rule CR1)
        have body_t': "body t'"
        proof -
          have "beta_reduce (Abs \<tau>\<^sub>1 t) (Abs \<tau>\<^sub>1 t')"
            by (meson beta_reduce.Abs body(2))
          then have "locally_closed (Abs \<tau>\<^sub>1 t')"
            by (rule locally_closed_if_beta_reduce[OF inf_vars])
          then show ?thesis
            by (simp add: locall_closed_Abs_iff_body)
        qed
        have hyp_t': "Red_ty \<tau>\<^sub>2 (subst_bound 0 v t')"
          if "locally_closed v" and "Red_ty \<tau>\<^sub>1 v" for v
        proof -
          have "Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
            by (rule hyp_t[OF that])
          moreover have "beta_reduce (subst_bound 0 v t) (subst_bound 0 v t')"
            using inf_vars \<open>beta_reduce t t'\<close> \<open>locally_closed v\<close>
            by (rule beta_reduce_subst_bound_subst_bound)
          ultimately show ?thesis
            by (rule CR2)
        qed
        have "beta_reduce\<inverse>\<inverse> t' t"
          using \<open>beta_reduce t t'\<close> by (rule conversepI)
        then have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t') u)"
          by (rule outer_IH[OF _ SN_u body_t' lc_u red_u hyp_t'])
        then show ?thesis
          by (simp add: \<open>w = App (Abs \<tau>\<^sub>1 t') u\<close>)
      next
        case (arg u')
        have "locally_closed u'"
          by (rule locally_closed_if_beta_reduce[OF inf_vars \<open>beta_reduce u u'\<close>])
        moreover have "Red_ty \<tau>\<^sub>1 u'"
          using red_u \<open>beta_reduce u u'\<close> by (rule CR2)
        moreover have "beta_reduce\<inverse>\<inverse> u' u"
          using \<open>beta_reduce u u'\<close> by (rule conversepI)
        ultimately have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u')"
          using inner_IH by blast
        then show ?thesis
          by (simp add: \<open>w = App (Abs \<tau>\<^sub>1 t) u'\<close>)
      qed
    qed
  qed
qed

lemma Red_Abs:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed (Abs \<tau>\<^sub>1 t)"
  assumes hyp: "\<And>u. locally_closed u \<Longrightarrow> Red_ty \<tau>\<^sub>1 u \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 u t)"
  shows "Red_ty (TyFun \<tau>\<^sub>1 \<tau>\<^sub>2) (Abs \<tau>\<^sub>1 t)"
proof -
  have body_t: "body t"
    using assms(2) by (simp add: locall_closed_Abs_iff_body)
  have SN_t: "SN t"
  proof -
    have "SN (subst_bound 0 (Free undefined) t)"
      by (rule CR1[OF hyp[OF locally_closed.Free Red_Free[OF inf_vars]]])
    then show "SN t"
      by (rule SN_subst_bound_FreeD)
  qed
  have "SN (Abs \<tau>\<^sub>1 t)"
    using SN_t by (rule SN_Abs)
  moreover have "Red_ty \<tau>\<^sub>2 (App (Abs \<tau>\<^sub>1 t) u)"
    if "locally_closed u" and "Red_ty \<tau>\<^sub>1 u" for u
  proof (rule Red_Abs_aux[OF inf_vars])
    show "SN t" by (rule SN_t)
    show "SN u" using that(2) by (rule CR1)
    show "body t" by (rule body_t)
    show "locally_closed u" by (rule that(1))
    show "Red_ty \<tau>\<^sub>1 u" by (rule that(2))
    show "\<And>v. locally_closed v \<Longrightarrow> Red_ty \<tau>\<^sub>1 v \<Longrightarrow> Red_ty \<tau>\<^sub>2 (subst_bound 0 v t)"
      by (rule hyp)
  qed
  ultimately show ?thesis
    by simp
qed

text \<open>Inverting a \<open>\<beta>\<close>-step out of a constant: exactly one parameter is reduced.\<close>

lemma beta_reduce_ConstD:
  assumes "beta_reduce (Const c \<tau>s ts) v"
  obtains i t' where "i < length ts" and "beta_reduce (ts ! i) t'"
    and "v = Const c \<tau>s (ts[i := t'])"
  using assms by (auto elim: beta_reduce.cases)

text \<open>A constant is strongly normalizing once all its parameters are (converse of \<open>SN_ConstD\<close>). The
  key \<open>cons\<close> step is a double induction: on the head (reductions in it) and on the constant built
  from the tail (reductions in the remaining parameters).\<close>

lemma SN_Const_cons:
  assumes "SN a" and "SN (Const c \<tau>s bs)"
  shows "SN (Const c \<tau>s (a # bs))"
  using assms
proof (induction a arbitrary: bs rule: accp_induct_rule)
  case (1 a)
  note IH_a = "1.IH"
  from "1.prems" show ?case
  proof (induction "Const c \<tau>s bs" arbitrary: bs rule: accp_induct_rule)
    case 1
    note SN_bs = "1.hyps"(1) and IH_bs = "1.hyps"(2)
    show ?case
    proof (rule accpI)
      fix v assume "beta_reduce\<inverse>\<inverse> v (Const c \<tau>s (a # bs))"
      then have "beta_reduce (Const c \<tau>s (a # bs)) v"
        by simp
      then obtain i t' where "i < length (a # bs)" and "beta_reduce ((a # bs) ! i) t'"
        and v_eq: "v = Const c \<tau>s ((a # bs)[i := t'])"
        by (elim beta_reduce_ConstD)
      then show "SN v"
      proof (cases i)
        case 0
        then have "beta_reduce a t'" and "v = Const c \<tau>s (t' # bs)"
          using \<open>beta_reduce ((a # bs) ! i) t'\<close> v_eq by simp_all
        then show ?thesis
          using IH_a SN_bs by (metis conversepI)
      next
        case (Suc j)
        have "beta_reduce (Const c \<tau>s bs) (Const c \<tau>s (bs[j := t']))"
        proof (rule beta_reduce.Const)
          show "\<forall>t\<in>set bs. locally_closed t"
            using \<open>beta_reduce (Const c \<tau>s (a # bs)) v\<close> beta_reduce.cases by force
        next
          show "j < length bs" and "beta_reduce (bs ! j) t'"
            using Suc \<open>i < length (a # bs)\<close> \<open>beta_reduce ((a # bs) ! i) t'\<close> by simp_all
        qed
          
        moreover have "v = Const c \<tau>s (a # bs[j := t'])"
          using Suc v_eq by simp
        ultimately show ?thesis
          using IH_bs by (metis conversepI)
      qed
    qed
  qed
qed

lemma SN_Const:
  "(\<And>t. t \<in> set ts \<Longrightarrow> SN t) \<Longrightarrow> SN (Const c \<tau>s ts)"
proof (induction ts)
  case Nil
  show ?case
  proof (rule accpI)
    fix v assume "beta_reduce\<inverse>\<inverse> v (Const c \<tau>s [])"
    then show "SN v"
      by (auto elim: beta_reduce.cases)
  qed
next
  case (Cons a bs)
  show ?case
  proof (rule SN_Const_cons)
    show "SN a"
      using Cons.prems by fastforce
    show "SN (Const c \<tau>s bs)"
    proof (rule Cons.IH)
      fix t assume "t \<in> set bs"
      then show "SN t"
        using Cons.prems by fastforce
    qed
  qed
qed

text \<open>Core of the constant lemma: a strongly normalizing, locally closed constant is reducible at any
  type. Since \<open>Const\<close> is neutral we invoke \<^text>\<open>CR3\<close>; each reduct reduces one parameter, so it is again
  a constant that is strongly normalizing and locally closed, hence reducible by the induction hypothesis.\<close>

lemma Red_Const_aux:
  fixes ts :: "(_, _, '\<V>) preterm list"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "SN (Const c \<tau>s ts)" and "locally_closed (Const c \<tau>s ts)"
  shows "Red_ty \<tau> (Const c \<tau>s ts)"
  using assms(2-)
proof (induction "Const c \<tau>s ts" arbitrary: ts rule: accp_induct_rule)
  case 1
  note IH = "1.hyps"(2)
  show ?case
  proof (rule CR3[OF inf_vars])
    show "neutral (Const c \<tau>s ts)"
      by (simp add: neutral_def)
  next
    show "locally_closed (Const c \<tau>s ts)"
      using "1.prems" .
  next
    fix v assume bv: "beta_reduce (Const c \<tau>s ts) v"
    then obtain i t' where "i < length ts" and "beta_reduce (ts ! i) t'"
      and v_eq: "v = Const c \<tau>s (ts[i := t'])"
      by (elim beta_reduce_ConstD)
    have "locally_closed v"
      by (rule locally_closed_if_beta_reduce[OF inf_vars bv])
    moreover have "beta_reduce\<inverse>\<inverse> v (Const c \<tau>s ts)"
      using bv by (rule conversepI)
    ultimately show "Red_ty \<tau> v"
      unfolding v_eq using IH by blast
  qed
qed

lemma Red_Const:
  fixes ts :: "(_, _, '\<V>) preterm list"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "locally_closed (Const c \<tau>s ts)"
  assumes "\<forall>t \<in> set ts. SN t"
  shows "Red_ty \<tau> (Const c \<tau>s ts)"
proof (rule Red_Const_aux[OF inf_vars])
  show "SN (Const c \<tau>s ts)"
    using assms by (auto intro: SN_Const)
next
  show "locally_closed (Const c \<tau>s ts)"
    by (rule assms)
qed


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
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "x \<notin> free_vars t"
  assumes "\<And>y. locally_closed (\<theta> y)"
  shows "msubst (\<theta>(x := u)) (subst_bound n (Free x) t) = subst_bound n u (msubst \<theta> t)"
  sorry


section \<open>Fundamental theorem and strong normalization\<close>

text \<open>Every well-typed term is reducible under any reducible, locally closed substitution of its
  free variables.\<close>

lemma fundamental:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes "has_type \<C> \<F> t \<tau>"
  assumes "\<And>x. locally_closed (\<theta> x)"
  assumes "\<And>x. Red_ty (\<F> x) (\<theta> x)"
  shows "Red_ty \<tau> (msubst \<theta> t)"
  sorry

lemma SN_if_has_type:
  fixes t :: "(_, _, '\<V>) preterm"
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  assumes ht: "has_type \<C> \<F> t \<tau>"
  shows "SN t"
proof -
  have "Red_ty \<tau> (msubst Free t)"
  proof (rule fundamental[OF inf_vars ht])
    show "\<And>x. locally_closed (Free x)"
      by (rule locally_closed.Free)
  next
    show "\<And>x. Red_ty (\<F> x) (Free x)"
      by (rule Red_Free[OF inf_vars])
  qed
  then show "SN t"
    by (metis CR1 msubst_Free)
qed

proposition strong_normalization_of_typed_terms:
  assumes inf_vars: "infinite (UNIV :: '\<V> set)"
  shows "wfp_on {t :: (_, _, '\<V>) preterm. \<exists>\<C> \<F> \<tau>. has_type \<C> \<F> t \<tau>} beta_reduce\<inverse>\<inverse>"
  by (rule wfp_on_beta_reduce_if_SN) (auto intro: SN_if_has_type[OF inf_vars])

end
