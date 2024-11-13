theory Restricted_Order
  imports Main
begin

section \<open>Restricted Orders\<close>

locale relation_restriction = 
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and lift :: "'b \<Rightarrow> 'a"
  assumes inj_lift [intro]: "inj lift"
begin

definition R\<^sub>r :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "R\<^sub>r b b' \<equiv> R (lift b) (lift b')"

end

subsection \<open>Strict Orders\<close>

locale strict_order = 
  fixes
    less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes
    transp [intro]: "transp (\<prec>)" and
    asymp [intro]: "asymp (\<prec>)"
begin

abbreviation less_eq where "less_eq \<equiv> (\<prec>)\<^sup>=\<^sup>="

notation less_eq (infix "\<preceq>" 50)
 
sublocale order "(\<preceq>)" "(\<prec>)"
  by(rule order_reflclp_if_transp_and_asymp[OF transp asymp])

end

locale strict_order_restriction = 
  strict_order +
  relation_restriction where R = "(\<prec>)"
begin

abbreviation "less\<^sub>r \<equiv> R\<^sub>r"

lemmas less\<^sub>r_def = R\<^sub>r_def

notation less\<^sub>r (infix "\<prec>\<^sub>r" 50)

sublocale restriction: strict_order "(\<prec>\<^sub>r)"
  by unfold_locales (auto simp: R\<^sub>r_def transp_def)

abbreviation "less_eq\<^sub>r \<equiv> restriction.less_eq"
notation less_eq\<^sub>r (infix "\<preceq>\<^sub>r" 50)

end

subsection \<open>Wellfounded Strict Orders\<close>

locale restricted_wellfounded_strict_order = strict_order +
  fixes restriction
  assumes wfp [intro]: "wfp_on restriction (\<prec>)"

locale wellfounded_strict_order = 
  restricted_wellfounded_strict_order where restriction = UNIV

locale wellfounded_strict_order_restriction = 
  strict_order_restriction +
  restricted_wellfounded_strict_order where restriction = "range lift" and less = "(\<prec>)"
begin

sublocale restriction: wellfounded_strict_order "(\<prec>\<^sub>r)"
proof unfold_locales
  show "wfp (\<prec>\<^sub>r)"
    using wfp_on_if_convertible_to_wfp_on[OF wfp]
    unfolding R\<^sub>r_def
    by simp
qed

end

subsection \<open>Total Strict Orders\<close>

locale restricted_total_strict_order = strict_order +
  fixes restriction
  assumes totalp [intro]: "totalp_on restriction (\<prec>)"

locale total_strict_order = 
  restricted_total_strict_order where restriction = UNIV
begin

sublocale linorder "(\<preceq>)" "(\<prec>)"
  using totalpD
  by unfold_locales fastforce

end

locale total_strict_order_restriction = 
  strict_order_restriction + 
  restricted_total_strict_order where restriction = "range lift" and less = "(\<prec>)"
begin

sublocale restriction: total_strict_order "(\<prec>\<^sub>r)"
proof unfold_locales
  show "totalp (\<prec>\<^sub>r)"
    using totalp inj_lift
    unfolding R\<^sub>r_def totalp_on_def inj_def
    by blast
qed

end

locale restricted_wellfounded_total_strict_order = 
  restricted_wellfounded_strict_order + restricted_total_strict_order 

end
