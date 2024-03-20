theory Clause_Ordering
  imports Clausal_Calculus_Extra
begin

lemma antisymp_on_reflclp:
  assumes "asymp_on A R"
  shows "antisymp_on A R\<^sup>=\<^sup>="
proof (rule antisymp_onI)
  fix x y
  assume "x \<in> A" and "y \<in> A" and "R\<^sup>=\<^sup>= x y" and "R\<^sup>=\<^sup>= y x"
  show "x = y"
  proof (cases "x = y")
    case True
    thus ?thesis .
  next
    case False
    hence "R x y"
      using \<open>R\<^sup>=\<^sup>= x y\<close> by simp
    hence "\<not> R y x"
      using \<open>asymp_on A R\<close>[THEN asymp_onD, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>] by iprover
    moreover have "R y x"
      using \<open>R\<^sup>=\<^sup>= y x\<close> False by simp
    ultimately have False
      by contradiction
    thus ?thesis ..
  qed
qed

lemma order_reflclp_if_transp_and_asymp:
  assumes "transp R" and "asymp R"
  shows "class.order R\<^sup>=\<^sup>= R"
proof unfold_locales
  show "\<And>x y. R x y = (R\<^sup>=\<^sup>= x y \<and> \<not> R\<^sup>=\<^sup>= y x)"
    using \<open>asymp R\<close> asympD by fastforce
next
  show "\<And>x. R\<^sup>=\<^sup>= x x"
    by simp
next
  show "\<And>x y z. R\<^sup>=\<^sup>= x y \<Longrightarrow> R\<^sup>=\<^sup>= y z \<Longrightarrow> R\<^sup>=\<^sup>= x z"
    using transp_on_reflclp[OF \<open>transp R\<close>, THEN transpD] .
next
  show "\<And>x y. R\<^sup>=\<^sup>= x y \<Longrightarrow> R\<^sup>=\<^sup>= y x \<Longrightarrow> x = y"
    using antisymp_on_reflclp[OF \<open>asymp R\<close>, THEN antisympD] .
qed

locale clause_ordering =
  fixes
    less_trm :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[intro]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)"
begin

definition less_lit :: "'t uprod literal \<Rightarrow> 't uprod literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

definition less_cls :: "'t uprod clause \<Rightarrow> 't uprod clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

sublocale term_order: order "(\<prec>\<^sub>t)\<^sup>=\<^sup>=" "(\<prec>\<^sub>t)"
  using order_reflclp_if_transp_and_asymp transp_less_trm asymp_less_trm by metis

sublocale literal_order: order "(\<prec>\<^sub>l)\<^sup>=\<^sup>=" "(\<prec>\<^sub>l)"
proof (rule order_reflclp_if_transp_and_asymp)
  show "transp (\<prec>\<^sub>l)"
    using transp_less_trm
    by (metis (opaque_lifting) less_lit_def transp_def transp_multp)
next
  show "asymp (\<prec>\<^sub>l)"
  by (metis asympD asymp_less_trm asymp_multp\<^sub>H\<^sub>O asympI less_lit_def multp_eq_multp\<^sub>H\<^sub>O
      transp_less_trm)
qed

sublocale clause_order: order "(\<prec>\<^sub>c)\<^sup>=\<^sup>=" "(\<prec>\<^sub>c)"
proof (rule order_reflclp_if_transp_and_asymp)
  show "transp (\<prec>\<^sub>c)"
    by (simp add: less_cls_def transp_multp)
next
  show "asymp (\<prec>\<^sub>c)"
    by (simp add: less_cls_def asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)
qed

end

end