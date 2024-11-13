theory Multiset_Extension
  imports 
    Restricted_Order
    Multiset_Extra
begin

section \<open>Multiset Extensions\<close>

locale multiset_extension = order: strict_order +
  fixes to_mset :: "'b \<Rightarrow> 'a multiset"
begin

definition multiset_extension :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "multiset_extension b1 b2 \<equiv> multp (\<prec>) (to_mset b1) (to_mset b2)"

notation multiset_extension (infix "\<prec>\<^sub>m" 50)

sublocale strict_order "(\<prec>\<^sub>m)"
proof unfold_locales
  show "transp (\<prec>\<^sub>m)"
    using transp_multp[OF order.transp]
    unfolding multiset_extension_def transp_on_def
    by blast
next
  show "asymp (\<prec>\<^sub>m)"
    unfolding multiset_extension_def
    by (simp add: asympD asymp_multp\<^sub>H\<^sub>O asymp_onI multp_eq_multp\<^sub>H\<^sub>O)
qed

(*no_notation less_eq (infix "\<preceq>" 50)*)
notation less_eq (infix "\<preceq>\<^sub>m" 50)

end

subsection \<open>Wellfounded Multiset Extensions\<close>

(* TODO: Investigate if restricted wfp can be lifted  *)
locale wellfounded_multiset_extension = 
  order: wellfounded_strict_order +
  multiset_extension
begin

sublocale wellfounded_strict_order "(\<prec>\<^sub>m)"
proof unfold_locales
  show "wfp (\<prec>\<^sub>m)"
    unfolding multiset_extension_def
    using wfp_if_convertible_to_wfp[OF wfp_multp[OF order.wfp]]
    by meson
qed

end

subsection \<open>Total Multiset Extensions\<close>

locale restricted_total_multiset_extension = 
  base: restricted_total_strict_order + 
  multiset_extension +
  assumes inj_on_to_mset: "inj_on to_mset {b. set_mset (to_mset b) \<subseteq> restriction}"
begin

sublocale restricted_total_strict_order "(\<prec>\<^sub>m)" "{b. set_mset (to_mset b) \<subseteq> restriction}"
proof unfold_locales
  have "totalp_on {b. set_mset b \<subseteq> restriction} (multp (\<prec>))"
    using totalp_on_multp[OF base.totalp base.transp]
    by fastforce

  then show "totalp_on {b. set_mset (to_mset b) \<subseteq> restriction} (\<prec>\<^sub>m)"
    using inj_on_to_mset
    unfolding multiset_extension_def totalp_on_def inj_on_def
    by auto
qed

end

locale total_multiset_extension = 
  order: total_strict_order + 
  multiset_extension +
  assumes inj_to_mset: "inj to_mset"
begin

sublocale restricted_total_multiset_extension where restriction = UNIV
  by unfold_locales (simp add: inj_to_mset)

sublocale total_strict_order "(\<prec>\<^sub>m)"
  using totalp
  by unfold_locales simp

end

locale total_wellfounded_multiset_extension = 
  wellfounded_multiset_extension + total_multiset_extension

end
