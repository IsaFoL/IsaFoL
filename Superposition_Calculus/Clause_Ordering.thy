theory Clause_Ordering
  imports Clausal_Calculus_Extra
begin

locale clause_ordering =
  fixes
    less_trm :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[intro]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)"
begin

lemma irreflp_on_less_trm[simp]: "irreflp_on A (\<prec>\<^sub>t)"
  by (metis asympD asymp_less_trm irreflp_onI)

definition less_lit :: "'t uprod literal \<Rightarrow> 't uprod literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

definition less_cls :: "'t uprod clause \<Rightarrow> 't uprod clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

lemma transp_on_less_lit[simp]: "transp_on A (\<prec>\<^sub>l)"
  by (smt (verit, ccfv_SIG) less_lit_def transpE transp_less_trm transp_multp transp_onI)

lemma asymp_on_less_lit[simp]: "asymp_on A (\<prec>\<^sub>l)"
  by (metis asympD asymp_less_trm asymp_multp\<^sub>H\<^sub>O asymp_onI less_lit_def multp_eq_multp\<^sub>H\<^sub>O
      transp_less_trm)

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: less_cls_def transp_multp)

lemma asymp_less_cls[simp]: "asymp (\<prec>\<^sub>c)"
  by (simp add: less_cls_def asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)


sublocale term_order: order "(\<prec>\<^sub>t)\<^sup>=\<^sup>=" "(\<prec>\<^sub>t)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = ((\<prec>\<^sub>t)\<^sup>=\<^sup>= x y \<and> \<not> (\<prec>\<^sub>t)\<^sup>=\<^sup>= y x)"
    using asympD by fastforce
next
  show "\<And>x. (\<prec>\<^sub>t)\<^sup>=\<^sup>= x x"
    by simp
next
  show "\<And>x y z. (\<prec>\<^sub>t)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>t)\<^sup>=\<^sup>= y z \<Longrightarrow> (\<prec>\<^sub>t)\<^sup>=\<^sup>= x z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. (\<prec>\<^sub>t)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>t)\<^sup>=\<^sup>= y x \<Longrightarrow> x = y"
    by (metis (full_types) asympD asymp_less_trm sup2E)
qed

sublocale literal_order: order "(\<prec>\<^sub>l)\<^sup>=\<^sup>=" "(\<prec>\<^sub>l)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = ((\<prec>\<^sub>l)\<^sup>=\<^sup>= x y \<and> \<not> (\<prec>\<^sub>l)\<^sup>=\<^sup>= y x)"
    by (metis (mono_tags, lifting) asympD asymp_on_less_lit sup2E sup2I1)
next
  show "\<And>x. (\<prec>\<^sub>l)\<^sup>=\<^sup>= x x"
    by simp
next
  show "\<And>x y z. (\<prec>\<^sub>l)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>l)\<^sup>=\<^sup>= y z \<Longrightarrow> (\<prec>\<^sub>l)\<^sup>=\<^sup>= x z"
    by (meson transpE transp_on_less_lit transp_on_reflclp)
next
  show "\<And>x y. (\<prec>\<^sub>l)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>l)\<^sup>=\<^sup>= y x \<Longrightarrow> x = y"
    by (metis (full_types) asympD asymp_on_less_lit sup2E)
qed

sublocale clause_order: order "(\<prec>\<^sub>c)\<^sup>=\<^sup>=" "(\<prec>\<^sub>c)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = ((\<prec>\<^sub>c)\<^sup>=\<^sup>= x y \<and> \<not> (\<prec>\<^sub>c)\<^sup>=\<^sup>= y x)"
    by (metis (mono_tags, lifting) asympD asymp_less_cls sup2E sup2I1)
next
  show "\<And>x. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x x"
    by simp
next
  show "\<And>x y z. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= y z \<Longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= x z"
    by (meson transpE transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. (\<prec>\<^sub>c)\<^sup>=\<^sup>= x y \<Longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= y x \<Longrightarrow> x = y"
    by (metis (full_types) asympD asymp_less_cls sup2E)
qed

end

end