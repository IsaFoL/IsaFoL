theory Multiset_Extra
  imports "HOL-Library.Multiset"
begin
  
definition is_maximal_wrt where
  "is_maximal_wrt R x M \<longleftrightarrow> (\<forall>y \<in># M - {#x#}. \<not> (R x y))"


lemma multp_singleton_singleton[simp]: "transp R \<Longrightarrow> multp R {#x#} {#y#} \<longleftrightarrow> R x y"
  using one_step_implies_multp[of "{#y#}" "{#x#}" R "{#}", simplified]
  using multp_implies_one_step[of R "{#x#}" "{#y#}", simplified]
  by (metis (no_types, opaque_lifting) add_mset_eq_single multi_member_split union_is_single
      union_single_eq_member)

lemma multp_subset_supersetI: "transp R \<Longrightarrow> multp R A B \<Longrightarrow> C \<subseteq># A \<Longrightarrow> B \<subseteq># D \<Longrightarrow> multp R C D"
  by (metis subset_implies_multp subset_mset.antisym_conv2 transpE transp_multp)

lemma multp_double_doubleI:
  assumes "transp R" "multp R A B"
  shows "multp R (A + A) (B + B)"
  using multp_repeat_mset_repeat_msetI[OF \<open>transp R\<close> \<open>multp R A B\<close>, of 2]
  by (simp add: numeral_Bit0)

lemma multp_single_doubleI: "M \<noteq> {#} \<Longrightarrow> multp R M (M + M)"
  using one_step_implies_multp[of M "{#}" _ M, simplified] by simp

end